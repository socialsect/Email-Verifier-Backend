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

# ---------------------------------------------------------
# Logging
# ---------------------------------------------------------
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# ---------------------------------------------------------
# Flask
# ---------------------------------------------------------
app = Flask(__name__)

# ---------------------------------------------------------
# Config
# ---------------------------------------------------------
VERIFICATION_TIMEOUT = 10         # DNS + socket timeout (seconds)
SMTP_CONNECT_TIMEOUT = 12         # SMTP connect timeout
SMTP_CMD_TIMEOUT = 12             # (socket timeout covers SMTP commands)
MAX_WORKERS = 3                   # keep it modest; SMTP servers rate-limit
JOB_RETENTION_HOURS = 24
MAX_FILE_SIZE = 5 * 1024 * 1024
MAX_EMAILS_PER_JOB = 10000

# Our legit sender identity (you already configured DNS for this)
SENDER_DOMAIN = "verify.pikkipals.com"
SENDER_EMAIL = f"probe@{SENDER_DOMAIN}"

# Try at most this many MX hosts per domain (top N by priority)
MAX_MX_TO_TRY = 3

# Gentle per-domain throttle (seconds between probes)
PER_DOMAIN_MIN_GAP = 0.6

# ---------------------------------------------------------
# In-memory job store
# ---------------------------------------------------------
data = {}
data_lock = threading.Lock()

def cleanup_old_jobs():
    cutoff = datetime.now() - timedelta(hours=JOB_RETENTION_HOURS)
    with data_lock:
        expired_jobs = [job_id for job_id, job_data in data.items()
                        if job_data.get('created_at', datetime.now()) < cutoff]
        for job_id in expired_jobs:
            del data[job_id]
            logger.info(f"Cleaned up expired job: {job_id}")

def require_job_id(f):
    @wraps(f)
    def decorated_function(*args, **kwargs):
        job_id = request.args.get('job_id')
        if not job_id or job_id not in data:
            return jsonify({'error': 'Invalid or missing job ID'}), 404
        return f(job_id, *args, **kwargs)
    return decorated_function

# ---------------------------------------------------------
# CORS
# ---------------------------------------------------------
@app.after_request
def after_request(response):
    response.headers.add('Access-Control-Allow-Origin', '*')
    response.headers.add('Access-Control-Allow-Headers', 'Content-Type,Authorization')
    response.headers.add('Access-Control-Allow-Methods', 'GET,PUT,POST,DELETE,OPTIONS')
    return response

# ---------------------------------------------------------
# Validators / constants
# ---------------------------------------------------------
EMAIL_REGEX = re.compile(r'^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$')

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

# Providers that commonly hide RCPT status / act accept-all
HIDDEN_STATUS_MX_SUFFIXES = (
    "aspmx.l.google.com", "googlemail.com",
    "protection.outlook.com",
    "yahoodns.net",
    "icloud-mail.com",
    "mx.zoho.com", "mx.zohomail.com",
    "mx.yandex.net",
    "mail.protonmail.ch", "protonmail.ch"
)

# ---------------------------------------------------------
# Verifier
# ---------------------------------------------------------
class EmailVerifier:
    def __init__(self):
        self.results = {}
        self.dns_resolver = dns.resolver.Resolver()
        self.dns_resolver.nameservers = ['8.8.8.8', '1.1.1.1', '9.9.9.9']
        self.dns_resolver.timeout = VERIFICATION_TIMEOUT
        self.dns_resolver.lifetime = VERIFICATION_TIMEOUT
        self._last_probe = {}  # domain -> last timestamp

    # ---------- Basic checks ----------
    def check_syntax(self, email):
        if not email or len(email) > 254:
            return False, "Email too long or empty"
        if not EMAIL_REGEX.match(email):
            return False, "Invalid email format"
        if '..' in email:
            return False, "Consecutive dots not allowed"
        local_part = email.split('@', 1)[0]
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
        """Return (True, [mx hosts...]) or (True, [domain]) if A fallback; else (False, reason)."""
        try:
            mx_records = self.dns_resolver.resolve(domain, 'MX')
            mx_sorted = sorted(mx_records, key=lambda x: x.preference)
            hosts = [str(r.exchange).rstrip('.') for r in mx_sorted]
            if hosts:
                return True, hosts
        except (dns.resolver.NXDOMAIN, dns.resolver.NoAnswer):
            pass
        except Exception as e:
            logger.warning(f"MX lookup error for {domain}: {e}")

        # RFC fallback to A record
        try:
            a_records = self.dns_resolver.resolve(domain, 'A')
            if a_records:
                return True, [domain]
        except Exception as e:
            logger.warning(f"A record lookup error for {domain}: {e}")

        return False, "No valid DNS records found"

    # ---------- SMTP probing ----------
    def _throttle_domain(self, domain):
        now = time.time()
        last = self._last_probe.get(domain, 0.0)
        gap = now - last
        if gap < PER_DOMAIN_MIN_GAP:
            time.sleep(PER_DOMAIN_MIN_GAP - gap)
        self._last_probe[domain] = time.time()

    def check_smtp_one_host(self, email, mx_host):
        """
        Real SMTP RCPT probe against a single host.
        Returns (verdict, message):
          verdict True  => mailbox accepted (and domain not catch-all)
          verdict False => explicit rejection (5xx)
          verdict None  => unknown (4xx/timeout/policy/accept-all)
        """
        target = email.strip()
        domain = target.split("@", 1)[-1].lower()

        # Certain providers never reveal validity; treat as unknown
        for suf in HIDDEN_STATUS_MX_SUFFIXES:
            if mx_host.endswith(suf):
                return None, f"{mx_host}: provider hides status"

        local_helo = f"probe-{uuid.uuid4().hex[:8]}.{SENDER_DOMAIN}"
        ctx = ssl.create_default_context()

        try:
            with smtplib.SMTP(host=mx_host, port=25, timeout=SMTP_CONNECT_TIMEOUT, local_hostname=local_helo) as smtp:
                smtp.set_debuglevel(0)

                # some providers don't like super-short timeouts
                socket.setdefaulttimeout(SMTP_CMD_TIMEOUT)

                code, resp = smtp.ehlo_or_helo_if_needed()
                if code >= 400:
                    return None, f"{mx_host}: EHLO/HELO rejected {code}"

                if smtp.has_extn("starttls"):
                    try:
                        smtp.starttls(context=ctx)
                        smtp.ehlo()
                    except smtplib.SMTPException:
                        # continue without TLS if STARTTLS fails
                        pass

                code, resp = smtp.mail(SENDER_EMAIL)
                if code >= 400:
                    return None, f"{mx_host}: MAIL FROM rejected {code}"

                # First RCPT
                code, resp = smtp.rcpt(target)
                msg = f"{mx_host}: RCPT {code}"

                if 200 <= code < 300:
                    # Possible catch-all: test two random RCPTs
                    import random, string
                    fake1 = ''.join(random.choices(string.ascii_lowercase, k=12)) + "@" + domain
                    fake2 = ''.join(random.choices(string.ascii_lowercase, k=12)) + "@" + domain
                    c1, _ = smtp.rcpt(fake1)
                    c2, _ = smtp.rcpt(fake2)
                    if (200 <= c1 < 300) and (200 <= c2 < 300):
                        return None, f"{msg} | domain appears catch-all"
                    return True, msg

                if 400 <= code < 500:
                    return None, msg  # greylist/temporary

                if code >= 500:
                    return False, msg  # explicit rejection

                return None, msg

        except (smtplib.SMTPServerDisconnected, smtplib.SMTPConnectError) as e:
            return None, f"{mx_host}: connect error {str(e)}"
        except (socket.timeout, TimeoutError):
            return None, f"{mx_host}: timeout"
        except Exception as e:
            return None, f"{mx_host}: exception {str(e)}"

    def smtp_probe_any_mx(self, email, domain, mx_hosts):
        """Try up to N MX hosts by priority; stop on definitive verdict."""
        tried = 0
        last_msg = ""
        for mx in mx_hosts[:MAX_MX_TO_TRY]:
            self._throttle_domain(domain)
            verdict, msg = self.check_smtp_one_host(email, mx)
            last_msg = msg
            if verdict is True or verdict is False:
                return verdict, msg
        return None, last_msg or "All MXs returned unknown"

    # ---------- Public API ----------
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

            ok, msg = self.check_syntax(email)
            if not ok:
                result['details'].append(f"Syntax: {msg}")
                return result

            result['confidence'] = 20
            local, domain = email.split('@', 1)
            domain = domain.lower()
            local = local.lower()

            if local in ROLE_BASED_PREFIXES:
                result['status'] = 'risky'
                result['confidence'] = 30
                result['details'].append("Role-based email address")
                return result

            ok, msg = self.check_disposable(domain)
            if not ok:
                result['details'].append(f"Disposable: {msg}")
                result['confidence'] = 10
                return result

            result['confidence'] = 50
            ok, mx_info = self.check_mx_records(domain)
            if not ok:
                result['details'].append(f"DNS: {mx_info}")
                result['confidence'] = 20
                return result

            result['confidence'] = 70
            result['details'].append(f"Mail servers: {', '.join(mx_info[:3])}{' ...' if len(mx_info) > 3 else ''}")

            # Real SMTP probe across MXes
            verdict, smtp_msg = self.smtp_probe_any_mx(email, domain, mx_info)

            if verdict is True:
                result['is_valid'] = True
                result['status'] = 'valid'
                result['confidence'] = 97
                result['details'].append(f"SMTP: {smtp_msg}")
            elif verdict is False:
                result['is_valid'] = False
                result['status'] = 'invalid'
                result['confidence'] = 90
                result['details'].append(f"SMTP: {smtp_msg}")
            else:
                # unknown / catch-all / greylist / policy / hidden providers
                result['is_valid'] = False
                result['status'] = 'risky'
                result['confidence'] = 60
                result['details'].append(f"SMTP: {smtp_msg}")

            return result

        except Exception as e:
            logger.exception("verify_email error")
            result['details'].append(f"Error: {str(e)}")
            result['status'] = 'error'
            result['confidence'] = 0
            return result

# ---------------------------------------------------------
# Instance
# ---------------------------------------------------------
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

# ---------------------------------------------------------
# Routes
# ---------------------------------------------------------
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
