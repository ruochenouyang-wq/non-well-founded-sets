#!/usr/bin/env python3
"""Check the curated publication after a successful clean Lean verification."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parent
VERIFY = ROOT / 'verification'
REPORT = VERIFY / 'content-audit.json'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    manifest = json.loads((VERIFY / 'proof-manifest.json').read_text())
    baseline = json.loads((VERIFY / 'source-baseline.json').read_text())
    assert manifest['status'] == 'PASS', 'Clean verification has not passed'
    assert manifest['verifier_sha256'] == sha(ROOT / 'lean/verify.py')
    assert manifest['toolchain_sha256'] == sha(ROOT / 'lean-toolchain')
    assert manifest['named_theorems'] == baseline['named_theorems'] == 1656
    assert manifest['modules'] == baseline['modules']
    assert len(manifest['modules']) == 340
    for entry in manifest['modules']:
        assert sha(ROOT / 'lean' / entry['file']) == entry['sha256'], entry['file']
    checks = {
        'cjk_characters': re.compile(r'[\u3400-\u9fff]'),
        'machine_specific_paths': re.compile('/' + r'(?:Users|home|private/var|private/tmp|tmp)/'),
        'private_key_header': re.compile(r'-----BEGIN (?:RSA |EC |OPENSSH )?PRIVATE KEY-----'),
        'github_token_pattern': re.compile(r'gh[pousr]_[A-Za-z0-9]{30,}'),
        'aws_access_key_pattern': re.compile(r'AKIA[0-9A-Z]{16}'),
    }
    issues = []
    files = {}
    links_checked = 0
    for p in sorted(ROOT.rglob('*')):
        if not p.is_file() or p == REPORT or '.git' in p.parts or '__pycache__' in p.parts:
            continue
        rel = p.relative_to(ROOT).as_posix()
        assert rel.isascii(), 'Non-ASCII filename: ' + rel
        content = p.read_text(encoding='utf-8')
        files[rel] = sha(p)
        for label, pattern in checks.items():
            if pattern.search(content):
                issues.append({'file': rel, 'check': label})
        if p.suffix == '.md':
            for target in re.findall(r'\]\(([^)]+)\)', content):
                if re.match(r'https?://', target):
                    continue
                path, _, anchor = target.partition('#')
                dest = (p.parent / path).resolve() if path else p
                assert dest.is_relative_to(ROOT), (rel, target)
                assert dest.is_file(), (rel, target)
                if re.fullmatch(r'L\d+', anchor):
                    assert 0 < int(anchor[1:]) <= len(dest.read_text().splitlines())
                links_checked += 1
    assert not issues, issues
    REPORT.write_text(json.dumps({
        'status': 'PASS', 'review_date': '2026-10-24',
        'lean_status': manifest['status'], 'modules': 340, 'named_theorems': 1656,
        'source_bytes_unchanged': True, 'filename_screening': 'ASCII filenames only',
        'text_checks': list(checks), 'local_markdown_links_checked': links_checked,
        'review_scope': 'English publication prose manually reviewed; automated pattern screening is limited to the listed checks. External links are not network-tested by this script.',
        'publication_operations_outside_audit_scope': True,
        'remaining_metadata': ['separate author attribution', 'reuse license'],
        'files_sha256': files,
    }, indent=2) + '\n')
    print(f'PASS: {len(files)} files screened; {links_checked} local links checked; 340 unchanged Lean modules.')


if __name__ == '__main__':
    main()
