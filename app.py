import csv
import dns.resolver
import re
import smtplib
import socket
import time
import uuid
import io
import logging
import whois
import threading
from datetime import datetime
from functools import lru_cache
from flask import Flask, request, jsonify, send_file

# ------------------- Logging -------------------
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# ------------------- Verifier Class -------------------
class EnhancedEmailVerifier:
    def __init__(self):
        self.results = {}
        self.dns_resolver = dns.resolver.Resolver()
        self.dns_resolver.nameservers = ['8.8.8.8', '1.1.1.1', '9.9.9.9']
        self.dns_resolver.timeout = 10
        self.dns_resolver.lifetime = 10

        # Cache for performance
        self.mx_cache = {}
        self.domain_rep_cache = {}
        self.catch_all_cache = {}

        # Default thresholds
        self.domain_age_suspicious = 14     # days
        self.domain_age_new = 90            # days
        self.disposable_domains = {"mailinator.com", "guerrillamail.com", "tempmail.com"}
        self.smtp_timeout = 10
        self.smtp_delay = 1
        self.max_smtp_retries = 3

        # Role-based prefixes
        self.role_prefixes = {
            "info", "support", "admin", "sales", "contact", "help", "service",
            "billing", "accounts", "marketing", "hr", "jobs", "careers", "press",
            "media", "legal", "compliance", "security", "webmaster", "postmaster",
            "noreply", "no-reply", "donotreply", "abuse", "feedback", "newsletter",
            "notifications", "alerts", "automated", "system", "daemon", "mailer"
        }

        # Your domain for SMTP HELO
        self.helo_domain = "gosocialsect.com"

        # Common domain typos
        self.common_domains = {
            'gmail.com': ['gmai.com', 'gmial.com', 'gmail.co', 'gmaill.com', 'gmil.com', 'gmal.com'],
            'yahoo.com': ['yaho.com', 'yahooo.com', 'yahoo.co', 'yhoo.com', 'ymail.com'],
            'outlook.com': ['outloo.com', 'outlook.co', 'outlok.com'],
            'hotmail.com': ['hotmial.com', 'hotmai.com', 'hotmall.com'],
            'aol.com': ['aol.co', 'aoil.com', 'aoll.com'],
            'icloud.com': ['iclou.com', 'icloud.co', 'iclod.com'],
            'protonmail.com': ['protonmai.com', 'protonmail.co', 'proton.com']
        }

    # ------------------- Email Checks -------------------
    def check_syntax(self, email):
        if not email or len(email) > 254:
            return False, "Email too long or empty"
        email_pattern = r'^[a-zA-Z0-9!#$%&\'*+/=?^_`{|}~-]+(?:\.[a-zA-Z0-9!#$%&\'*+/=?^_`{|}~-]+)*@[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?(?:\.[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?)*$'
        if not re.match(email_pattern, email):
            return False, "Invalid email format"
        if '..' in email or email.startswith('.') or email.endswith('.'):
            return False, "Invalid dot placement"
        local, domain = email.split('@')
        if len(local) > 64:
            return False, "Local part too long"
        if len(domain) > 253:
            return False, "Domain part too long"
        return True, "Valid syntax"

    def suggest_domain_correction(self, domain):
        from difflib import get_close_matches
        domain_lower = domain.lower()
        for correct, typos in self.common_domains.items():
            if domain_lower in typos:
                return correct
        matches = get_close_matches(domain_lower, self.common_domains.keys(), n=1, cutoff=0.8)
        return matches[0] if matches else None

    @lru_cache(maxsize=1000)
    def check_mx_records_cached(self, domain):
        try:
            mx_records = self.dns_resolver.resolve(domain, 'MX')
            if mx_records:
                sorted_mx = sorted(mx_records, key=lambda x: x.preference)
                return True, str(sorted_mx[0].exchange).rstrip('.'), [str(mx.exchange).rstrip('.') for mx in sorted_mx[:3]]
        except Exception:
            pass
        try:
            a_records = self.dns_resolver.resolve(domain, 'A')
            if a_records:
                return True, domain, [domain]
        except Exception:
            pass
        return False, "No valid DNS records found", []

    def check_domain_reputation(self, domain):
        if domain in self.domain_rep_cache:
            return self.domain_rep_cache[domain]
        result = {"age_days": None, "is_suspicious": False, "reason": ""}
        try:
            w = whois.whois(domain)
            created = w.creation_date
            if created:
                if isinstance(created, list):
                    created = created[0]
                age_days = (datetime.now() - created).days
                result["age_days"] = age_days
                if age_days < self.domain_age_suspicious:
                    result["is_suspicious"] = True
                    result["reason"] = f"Domain too new ({age_days} days)"
                elif age_days < self.domain_age_new:
                    result["reason"] = f"Domain relatively new ({age_days} days)"
        except Exception:
            result["reason"] = "Could not determine domain age"
        self.domain_rep_cache[domain] = result
        return result

    def check_smtp_connection(self, email, mx_record, timeout=None):
        if timeout is None:
            timeout = self.smtp_timeout
        try:
            time.sleep(self.smtp_delay)
            server = smtplib.SMTP(timeout=timeout)
            server.connect(mx_record, 25)
            try:
                server.ehlo(self.helo_domain)
            except:
                server.helo(self.helo_domain)
            server.mail(f"test@{self.helo_domain}")
            code, message = server.rcpt(email)
            server.quit()
            if code == 250: return True, "Mailbox exists"
            if code == 251: return True, "Forwarded"
            if code in [550, 551, 553]: return False, "Mailbox doesn't exist"
            return None, "Uncertain"
        except Exception as e:
            return None, f"SMTP error: {e}"

    def verify_email_enhanced(self, email):
        result = {'email': email, 'is_valid': False, 'status': 'invalid',
                  'details': [], 'confidence': 0, 'suggestions': []}
        try:
            valid, msg = self.check_syntax(email)
            if not valid:
                result['details'].append(f"Syntax: {msg}")
                return result
            local, domain = email.split('@')
            domain = domain.lower(); local = local.lower()
            suggestion = self.suggest_domain_correction(domain)
            if suggestion:
                result['suggestions'].append(f"{local}@{suggestion}")
                return result
            if local in self.role_prefixes:
                result['status'] = 'risky'
                result['details'].append("Role-based address")
            if domain in self.disposable_domains:
                result['details'].append("Disposable domain")
                return result
            domain_rep = self.check_domain_reputation(domain)
            if domain_rep["is_suspicious"]:
                result['status'] = 'risky'
                result['details'].append(domain_rep["reason"])
            valid, mx_info, _ = self.check_mx_records_cached(domain)
            if not valid:
                result['details'].append(f"DNS: {mx_info}")
                return result
            smtp_valid, smtp_msg = self.check_smtp_connection(email, mx_info)
            if smtp_valid:
                result['is_valid'] = True
                result['status'] = 'valid'
                result['details'].append(smtp_msg)
            elif smtp_valid is False:
                result['details'].append(smtp_msg)
            else:
                result['status'] = 'risky'
                result['details'].append(smtp_msg)
        except Exception as e:
            result['details'].append(f"Error: {e}")
        return result

# ------------------- Flask Integration -------------------
app = Flask(__name__)
verifier = EnhancedEmailVerifier()
jobs = {}

def update_job_progress(job_id, valid, risky, invalid, message, status):
    jobs[job_id].update({
        "valid": valid, "risky": risky, "invalid": invalid,
        "message": message, "status": status
    })

def process_file(file, job_id, email_field="email"):
    try:
        content = file.read().decode('utf-8-sig')
        reader = list(csv.DictReader(io.StringIO(content)))
        results = []
        valid_count = risky_count = invalid_count = 0
        for i, row in enumerate(reader, 1):
            email = (row.get(email_field) or '').strip()
            if not email:
                result = {"status": "invalid", "details": "Empty email"}
                invalid_count += 1
            else:
                result = verifier.verify_email_enhanced(email)
                if result["status"] == "valid": valid_count += 1
                elif result["status"] == "risky": risky_count += 1
                else: invalid_count += 1
            results.append({**row, **result})
            if i % 10 == 0 or i == len(reader):
                update_job_progress(job_id, valid_count, risky_count, invalid_count,
                                    f"{i}/{len(reader)} processed", "in-progress")
        jobs[job_id]["results"] = results
        update_job_progress(job_id, valid_count, risky_count, invalid_count,
                            "Completed", "done")
    except Exception as e:
        update_job_progress(job_id, 0, 0, 0, str(e), "error")

# ------------------- Endpoints -------------------
@app.route("/upload", methods=["POST"])
def upload_file():
    if 'file' not in request.files:
        return jsonify({"error": "No file"}), 400
    file = request.files['file']
    job_id = str(uuid.uuid4())
    jobs[job_id] = {"status": "starting", "results": []}
    threading.Thread(target=process_file, args=(file, job_id)).start()
    return jsonify({"job_id": job_id})

@app.route("/status/<job_id>", methods=["GET"])
def check_status(job_id):
    return jsonify(jobs.get(job_id, {"error": "Invalid job ID"}))

@app.route("/results/<job_id>", methods=["GET"])
def get_results(job_id):
    job = jobs.get(job_id)
    if not job: return jsonify({"error": "Invalid job ID"}), 404
    return jsonify(job.get("results", []))

@app.route("/download/<job_id>", methods=["GET"])
def download_results(job_id):
    job = jobs.get(job_id)
    if not job or "results" not in job:
        return jsonify({"error": "Invalid job ID or no results"}), 404
    output = io.StringIO()
    writer = csv.DictWriter(output, fieldnames=job["results"][0].keys())
    writer.writeheader()
    writer.writerows(job["results"])
    output.seek(0)
    return send_file(io.BytesIO(output.getvalue().encode("utf-8")),
                     mimetype="text/csv", as_attachment=True,
                     download_name=f"results_{job_id}.csv")

@app.route("/cancel/<job_id>", methods=["POST"])
def cancel_job(job_id):
    if job_id in jobs:
        jobs[job_id]["cancelled"] = True
        return jsonify({"message": f"Job {job_id} cancelled"})
    return jsonify({"error": "Invalid job ID"}), 404

@app.route("/verify-single", methods=["GET"])
def verify_single():
    email = request.args.get("email")
    if not email:
        return jsonify({"error": "Email required"}), 400
    result = verifier.verify_email_enhanced(email)
    result["deliverability"] = "YES" if result.get("is_valid") else "NO"
    return jsonify(result)

# ------------------- Run -------------------
if __name__ == "__main__":
    app.run(debug=True, port=5000)
