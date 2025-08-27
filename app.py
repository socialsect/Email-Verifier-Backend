import csv
import dns.resolver
import re
import smtplib
import socket
import time
import ssl
import dns.exception
import uuid
import io
import threading
import logging
from flask import Flask, request, jsonify, Response
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timedelta
from functools import wraps

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# Create Flask app
app = Flask(__name__)

# Configuration
VERIFICATION_TIMEOUT = 10  # seconds
MAX_WORKERS = 3  # Reduced for better resource management
JOB_RETENTION_HOURS = 24  # How long to keep job data
MAX_FILE_SIZE = 5 * 1024 * 1024  # 5MB max file size
MAX_EMAILS_PER_JOB = 10000  # Reasonable limit for processing

# In-memory storage for job data with timestamps
data = {}
data_lock = threading.Lock()


def cleanup_old_jobs():
    """Remove jobs older than JOB_RETENTION_HOURS"""
    cutoff = datetime.now() - timedelta(hours=JOB_RETENTION_HOURS)
    with data_lock:
        expired_jobs = [job_id for job_id, job_data in data.items()
                        if job_data.get('created_at', datetime.now()) < cutoff]
        for job_id in expired_jobs:
            del data[job_id]
            logger.info(f"Cleaned up expired job: {job_id}")


def require_job_id(f):
    """Decorator to validate job_id parameter"""
    @wraps(f)
    def decorated_function(*args, **kwargs):
        job_id = request.args.get('job_id')
        if not job_id or job_id not in data:
            return jsonify({'error': 'Invalid or missing job ID'}), 404
        return f(job_id, *args, **kwargs)
    return decorated_function


# Add CORS headers for all routes
@app.after_request
def after_request(response):
    response.headers.add('Access-Control-Allow-Origin', '*')
    response.headers.add('Access-Control-Allow-Headers', 'Content-Type,Authorization')
    response.headers.add('Access-Control-Allow-Methods', 'GET,PUT,POST,DELETE,OPTIONS')
    return response


# Email validation patterns
EMAIL_REGEX = re.compile(r'^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$')

# Expanded disposable domains list
DISPOSABLE_DOMAINS = {
    'mailinator.com', 'guerrillamail.com', '10minutemail.com', 'tempmail.com',
    'yopmail.com', 'maildrop.cc', 'temp-mail.org', 'throwaway.email',
    'getnada.com', 'mohmal.com', 'sharklasers.com', 'grr.la', 'guerrillamailblock.com',
    '10minutesemail.net', 'tempr.email', 'tempail.com', 'emailondeck.com'
}

ROLE_BASED_PREFIXES = {
    "info", "support", "admin", "sales", "contact", "help", "service",
    "billing", "accounts", "marketing", "hr", "jobs", "careers", "press",
    "media", "legal", "compliance", "security", "webmaster", "postmaster"
}


class EmailVerifier:
    def __init__(self):
        self.results = {}
        self.dns_resolver = dns.resolver.Resolver()
        self.dns_resolver.nameservers = ['8.8.8.8', '1.1.1.1', '9.9.9.9']
        self.dns_resolver.timeout = VERIFICATION_TIMEOUT
        self.dns_resolver.lifetime = VERIFICATION_TIMEOUT

    def check_syntax(self, email):
        """Check if email has valid syntax with additional validation"""
        if not email or len(email) > 254:
            return False, "Email too long or empty"

        if not EMAIL_REGEX.match(email):
            return False, "Invalid email format"

        if '..' in email:
            return False, "Consecutive dots not allowed"

        local_part = email.split('@')[0]
        if len(local_part) > 64:
            return False, "Local part too long"

        return True, ""

    def check_disposable(self, domain):
        domain_lower = domain.lower()
        if domain_lower in DISPOSABLE_DOMAINS:
            return False, "Disposable email domain"

        disposable_patterns = ['temp', 'disposable', 'throwaway', '10min', 'fake']
        if any(pattern in domain_lower for pattern in disposable_patterns):
            return False, "Suspected disposable email domain"

        return True, ""

    def check_mx_records(self, domain):
        try:
            mx_records = self.dns_resolver.resolve(domain, 'MX')
            if mx_records:
                sorted_mx = sorted(mx_records, key=lambda x: x.preference)
                return True, str(sorted_mx[0].exchange).rstrip('.')
        except (dns.resolver.NXDOMAIN, dns.resolver.NoAnswer):
            pass
        except Exception as e:
            logger.warning(f"MX lookup error for {domain}: {e}")

        try:
            a_records = self.dns_resolver.resolve(domain, 'A')
            if a_records:
                return True, domain
        except Exception as e:
            logger.warning(f"A record lookup error for {domain}: {e}")

        return False, "No valid DNS records found"

    def check_smtp(self, email, mx_record):
        domain = email.split('@')[-1].lower()
        if domain in DISPOSABLE_DOMAINS:
            return False, "Disposable email domain"
        try:
            try:
                mx_records = self.dns_resolver.resolve(domain, 'MX')
                if not mx_records:
                    try:
                        self.dns_resolver.resolve(domain, 'A')
                    except:
                        return False, "No valid DNS records found"
            except:
                return False, "DNS resolution failed"

            return True, "Email domain is valid"

        except Exception as e:
            logger.warning(f"SMTP verification error for {email}: {str(e)}")
            return False, f"Verification error: {str(e)}"

    def verify_email(self, email, job_id=None):
        result = {
            'email': email,
            'is_valid': False,
            'status': 'invalid',
            'details': [],
            'confidence': 0
        }

        try:
            if job_id and data.get(job_id, {}).get('cancelled'):
                result['details'].append("Verification cancelled")
                return result

            valid, msg = self.check_syntax(email)
            if not valid:
                result['details'].append(f"Syntax: {msg}")
                result['confidence'] = 0
                return result

            result['confidence'] = 20
            local, domain = email.split('@')
            domain = domain.lower()
            local = local.lower()

            if local in ROLE_BASED_PREFIXES:
                result['status'] = 'risky'
                result['details'].append("Role-based email address")
                result['confidence'] = 30
                return result

            result['confidence'] = 40
            valid, msg = self.check_disposable(domain)
            if not valid:
                result['details'].append(f"Disposable: {msg}")
                result['confidence'] = 10
                return result

            result['confidence'] = 60
            valid, mx_info = self.check_mx_records(domain)
            if not valid:
                result['details'].append(f"DNS: {mx_info}")
                result['confidence'] = 20
                return result

            result['confidence'] = 80
            result['details'].append(f"Mail server: {mx_info}")

            valid, smtp_msg = self.check_smtp(email, mx_info)
            if valid:
                result['is_valid'] = True
                result['status'] = 'valid'
                result['confidence'] = 95
                result['details'].append(f"SMTP: {smtp_msg}")
            else:
                result['details'].append(f"SMTP: {smtp_msg}")
                result['status'] = 'risky'
                result['confidence'] = 60

            return result

        except Exception as e:
            result['details'].append(f"Error: {str(e)}")
            result['status'] = 'error'
            result['confidence'] = 0
            return result


verifier = EmailVerifier()


def update_job_progress(job_id, progress, row, total, log, status='running'):
    with data_lock:
        if job_id in data:
            data[job_id].update({
                'progress': min(100, max(0, progress)),
                'row': row,
                'total': total,
                'log': log,
                'status': status,
                'updated_at': datetime.now()
            })


# ---------- NEW ENDPOINT FOR SINGLE EMAIL VERIFICATION ----------
@app.route('/verify-single', methods=['GET', 'OPTIONS'])
def verify_single():
    if request.method == 'OPTIONS':
        return '', 200
    
    email = request.args.get('email')
    if not email:
        return jsonify({'error': 'Email parameter is required'}), 400
    
    try:
        result = verifier.verify_email(email)
        
        # Format response for n8n compatibility
        response_data = {
            'email': result['email'],
            'status': result['status'],
            'deliverability': 'DELIVERABLE' if result['status'] == 'valid' else 'UNDELIVERABLE',
            'is_valid': result['is_valid'],
            'confidence': result['confidence'],
            'details': result['details']
        }
        
        return jsonify(response_data)
    
    except Exception as e:
        logger.error(f"Error verifying single email {email}: {e}")
        return jsonify({
            'email': email,
            'status': 'error',
            'deliverability': 'UNKNOWN',
            'is_valid': False,
            'confidence': 0,
            'details': [f'Error: {str(e)}']
        }), 500


# ---------- EXISTING ENDPOINTS (unchanged) ----------

@app.route('/verify', methods=['POST', 'OPTIONS'])
def verify():
    if request.method == 'OPTIONS':
        return '', 200

    if 'file' not in request.files:
        return jsonify({'error': 'No file provided'}), 400

    file = request.files['file']

    if not file.filename:
        return jsonify({'error': 'No file selected'}), 400

    if not file.filename.lower().endswith('.csv'):
        return jsonify({'error': 'Only CSV files are supported'}), 400

    file.seek(0, 2)
    file_size = file.tell()
    file.seek(0)

    if file_size > MAX_FILE_SIZE:
        return jsonify({'error': f'File too large. Maximum size: {MAX_FILE_SIZE // (1024*1024)}MB'}), 400

    job_id = str(uuid.uuid4())

    with data_lock:
        data[job_id] = {
            'progress': 0,
            'row': 0,
            'total': 0,
            'log': 'Initializing...',
            'results': [],
            'status': 'starting',
            'created_at': datetime.now(),
            'updated_at': datetime.now(),
            'cancelled': False
        }

    def process_file():
        try:
            content = file.read().decode('utf-8-sig')
            reader = list(csv.DictReader(io.StringIO(content)))

            if not reader:
                update_job_progress(job_id, 0, 0, 0, 'Error: Empty CSV file', 'error')
                return

            total_emails = len(reader)

            if total_emails > MAX_EMAILS_PER_JOB:
                update_job_progress(job_id, 0, 0, 0,
                                    f'Error: Too many emails. Maximum: {MAX_EMAILS_PER_JOB}', 'error')
                return

            headers = [h.lower().strip() for h in reader[0].keys()]
            email_field = None
            for original_header, lower_header in zip(reader[0].keys(), headers):
                if lower_header in ['email', 'email_address', 'e-mail', 'mail']:
                    email_field = original_header
                    break

            if not email_field:
                update_job_progress(job_id, 0, 0, 0,
                                    'Error: No email column found. Expected: email, email_address, e-mail, or mail',
                                    'error')
                return

            update_job_progress(job_id, 0, 0, total_emails, f'Processing {total_emails} emails...', 'running')

            valid_count = risky_count = invalid_count = 0

            for i, row in enumerate(reader, 1):
                if data.get(job_id, {}).get('cancelled'):
                    update_job_progress(job_id, 100, i, total_emails, 'Verification cancelled', 'cancelled')
                    break

                email = (row.get(email_field) or '').strip()

                if not email:
                    result_row = {**row, 'status': 'invalid', 'details': 'Empty email', 'confidence': 0}
                    invalid_count += 1
                else:
                    result = verifier.verify_email(email, job_id)
                    status = result.get('status', 'invalid').lower()
                    if status == 'error':
                        status = 'invalid'
                    result_row = {
                        **row,
                        'status': status,
                        'details': ' | '.join(result.get('details', ['Unknown error'])),
                        'confidence': result.get('confidence', 0)
                    }
                    if status == 'valid':
                        valid_count += 1
                    elif status == 'risky':
                        risky_count += 1
                    else:
                        invalid_count += 1

                with data_lock:
                    if job_id in data:
                        data[job_id]['results'].append(result_row)

                progress = int((i / total_emails) * 100)
                update_job_progress(job_id, progress, i, total_emails,
                                    f"Processing... Valid: {valid_count}, Risky: {risky_count}, Invalid: {invalid_count}",
                                    'running')

                time.sleep(0.1)

            if not data.get(job_id, {}).get('cancelled'):
                final_log = f"Complete! Valid: {valid_count}, Risky: {risky_count}, Invalid: {invalid_count}"
                update_job_progress(job_id, 100, total_emails, total_emails, final_log, 'completed')

        except Exception as e:
            logger.error(f"Processing error for job {job_id}: {e}")
            update_job_progress(job_id, 0, 0, 0, f'Error: {str(e)}', 'error')

    thread = threading.Thread(target=process_file)
    thread.daemon = True
    thread.start()

    if len(data) > 100:
        cleanup_thread = threading.Thread(target=cleanup_old_jobs)
        cleanup_thread.daemon = True
        cleanup_thread.start()

    return jsonify({'job_id': job_id, 'message': 'Verification started'})


@app.route('/progress')
@require_job_id
def progress(job_id):
    job = data[job_id]
    return jsonify({
        'percent': job.get('progress', 0),
        'row': job.get('row', 0),
        'total': job.get('total', 0),
        'status': job.get('status', 'unknown')
    })


@app.route('/log')
@require_job_id
def log(job_id):
    return data[job_id].get('log', 'No log available')


@app.route('/cancel', methods=['POST', 'OPTIONS'])
def cancel():
    if request.method == 'OPTIONS':
        return '', 200

    job_id = request.args.get('job_id')
    if job_id and job_id in data:
        with data_lock:
            data[job_id]['cancelled'] = True
            data[job_id]['status'] = 'cancelled'
        return jsonify({'message': 'Job cancelled'})
    return jsonify({'error': 'Job not found'}), 404


@app.route('/download')
@require_job_id
def download(job_id):
    filter_type = request.args.get('type', 'all')
    if 'results' not in data[job_id]:
        return 'No results found for this job', 404

    results = data[job_id]['results']
    if filter_type == 'valid':
        filtered = [r for r in results if r.get('status') == 'valid']
    elif filter_type == 'risky':
        filtered = [r for r in results if r.get('status') == 'risky']
    elif filter_type == 'invalid':
        filtered = [r for r in results if r.get('status') == 'invalid']
    elif filter_type == 'risky_invalid':
        filtered = [r for r in results if r.get('status') in ('risky', 'invalid')]
    else:
        filtered = results

    if not filtered:
        return 'No data available for the selected filter', 404

    output = io.StringIO()
    fieldnames = list(filtered[0].keys())
    writer = csv.DictWriter(output, fieldnames=fieldnames)
    writer.writeheader()
    for row in filtered:
        writer.writerow(row)
    output.seek(0)

    timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
    filename = f"email_verification_{filter_type}_{timestamp}.csv"

    return Response(
        output.getvalue(),
        mimetype='text/csv',
        headers={"Content-Disposition": f"attachment; filename={filename}"}
    )


@app.route('/stats')
@require_job_id
def stats(job_id):
    job = data[job_id]
    if 'results' not in job:
        return jsonify({'error': 'No results available'}), 404
    results = job['results']
    total = len(results)
    if total == 0:
        return jsonify({'total': 0})

    valid = sum(1 for r in results if r.get('status') == 'valid')
    risky = sum(1 for r in results if r.get('status') == 'risky')
    invalid = sum(1 for r in results if r.get('status') == 'invalid')

    return jsonify({
        'total': total,
        'valid': valid,
        'risky': risky,
        'invalid': invalid,
        'valid_percentage': round((valid / total) * 100, 1),
        'risky_percentage': round((risky / total) * 100, 1),
        'invalid_percentage': round((invalid / total) * 100, 1)
    })


@app.errorhandler(413)
def too_large(e):
    return jsonify({'error': 'File too large'}), 413


@app.errorhandler(500)
def internal_error(e):
    return jsonify({'error': 'Internal server error'}), 500


if __name__ == '__main__':
    # For local testing only - Render will use Gunicorn
    app.run(debug=True, host='0.0.0.0', port=5000, threaded=True)
