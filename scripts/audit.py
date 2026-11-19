#!/usr/bin/env python3
"""Build the Lean library and audit the declarations registered in its coverage inventory."""

import argparse
from hashlib import sha256
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
from tempfile import TemporaryDirectory

from check_dependencies import check as check_dependencies


def lean_code(text):
    """Remove nested block comments, line comments and strings for a keyword scan."""
    out = []
    i = 0
    depth = 0
    string = False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1
                i += 2
            elif text.startswith('-/', i):
                depth -= 1
                i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif string:
            if text[i] == '\\':
                i += 2
            elif text[i] == '"':
                string = False
                i += 1
            else:
                out.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif text.startswith('/-', i):
            depth = 1
            out.append(' ')
            i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            string = True
            out.append(' ')
            i += 1
        else:
            out.append(text[i])
            i += 1
    return ''.join(out)


def fail(message):
    raise RuntimeError(message)



def validate_terminal_scope(coverage, items):
    unfinished = [item['id'] for item in items if item['status'] != 'verified']
    if coverage.get('inventory_complete') is not True or unfinished or not items:
        fail('Formalization is incomplete. Complete the inventory and verify every entry. '
             'Open entries: ' + ', '.join(unfinished))
    if not coverage.get('paper_roots'):
        fail('No manuscript roots registered for terminal audit.')


def axiom_command(name):
    """Build the axiom check, including names with Lean's numeric components."""
    parts = name.split('.')
    if not any(part.isascii() and part.isdecimal() for part in parts):
        return '#print axioms ' + name
    # Private declaration names have numeric components that the parser cannot
    # read as identifiers. Pass the exact Name to the same command elaborator.
    expression = 'Lean.Name.anonymous'
    for part in parts:
        if part.isascii() and part.isdecimal():
            expression = f'(Lean.Name.num {expression} {int(part)})'
        else:
            expression = f'(Lean.Name.str {expression} {json.dumps(part, ensure_ascii=False)})'
    return ('run_cmd do\n'
            f'  let name := {expression}\n'
            '  Lean.Elab.Command.elabCommand (← `(#print axioms $(Lean.mkIdent name)))')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--terminal', action='store_true', help='require complete coverage and proofs')
    mode.add_argument('--snapshot', action='store_true',
                      help='check all implemented proofs and dependencies with deferred results recorded')
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    coverage = json.loads((root / 'lean/coverage.json').read_text())
    if args.snapshot or args.terminal:
        manuscript = root / coverage['source']
        if sha256(manuscript.read_bytes()).hexdigest() != coverage['source_sha256']:
            fail('Manuscript fingerprint differs from the reviewed source.')
    items = coverage.get('items', [])
    if not isinstance(items, list):
        fail('The coverage inventory is malformed.')
    ids = [item['id'] for item in items]
    if len(set(ids)) != len(ids):
        fail('Coverage IDs must be unique.')
    names = []
    for item in items:
        if item['status'] not in {'not_started', 'in_progress', 'verified'}:
            fail('Invalid status for ' + item['id'])
        name = item.get('declaration')
        if name:
            # Prevent newline or Lean-command injection in generated audit commands.
            if not isinstance(name, str) or re.search(r'[\s;`"\\]', name):
                fail('Expected a plain qualified declaration name for ' + item['id'])
            names.append(name)
        elif item['status'] == 'verified':
            fail('Verified entry has no declaration: ' + item['id'])
    names = list(dict.fromkeys(names))
    if args.terminal:
        validate_terminal_scope(coverage, items)
        if not names:
            fail('No declarations registered for terminal audit.')

    holes = []
    for path in sorted((root / 'lean').rglob('*.lean')):
        code = lean_code(path.read_text())
        for number, line in enumerate(code.splitlines(), 1):
            if re.search(r'\baxiom\b', line):
                fail(f'Project axiom declaration: {path.relative_to(root)}:{number}')
            if re.search(r'\b(sorry|admit|sorryAx)\b', line):
                holes.append(f'{path.relative_to(root)}:{number}')
    if holes:
        print('Unfinished proof terms: ' + ', '.join(holes), flush=True)
        if args.snapshot or args.terminal:
            fail('Proof placeholders remain.')

    if shutil.which('lake') is None:
        fail('Lake is unavailable. Run sh scripts/setup.sh first.')
    subprocess.run(['lake', 'build'], cwd=root, check=True)
    if args.snapshot or args.terminal:
        check_dependencies(root, include_deferred=args.snapshot)
    audit = 'import PaperFormalization\nimport Lean\n\n'
    audit += '-- Generated by scripts/audit.py from lean/coverage.json. Do not edit by hand.\n'
    if names:
        audit += '\n\n'.join(axiom_command(name) for name in names) + '\n'
    else:
        audit += '-- No declarations have been registered yet; this is not a proof certificate.\n'
    with TemporaryDirectory(prefix='paper-axioms-', dir=root / '.lake') as scratch:
        audit_path = Path(scratch) / 'Audit.lean'
        audit_path.write_text(audit)
        result = subprocess.run(['lake', 'env', 'lean', str(audit_path)], cwd=root,
                                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    print(result.stdout, end='', flush=True)
    if result.returncode:
        fail('Lean could not check the generated audit.')
    if not names:
        print('Build checked; no mathematical declarations are registered. Formalization not started.')
        return

    reports = {}
    for match in re.finditer(r"'([^\n]+)'\s+depends on axioms:\s*\[([^\]]*)\]", result.stdout):
        reports[match[1]] = {s.strip() for s in match[2].split(',') if s.strip()}
    for match in re.finditer(r"'([^\n]+)'\s+does not depend on any axioms", result.stdout):
        reports[match[1]] = set()
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    for name in names:
        if name not in reports:
            fail('Missing or unrecognized axiom report for ' + name)
        item_statuses = [i['status'] for i in items if i.get('declaration') == name]
        permitted = allowed if args.snapshot or args.terminal or 'verified' in item_statuses else allowed | {'sorryAx'}
        unexpected = reports[name] - permitted
        if unexpected:
            fail('Unexpected axioms for ' + name + ': ' + ', '.join(sorted(unexpected)))
    if args.terminal:
        print('Terminal mechanical audit passed. Source-to-statement review is also required.')
    elif args.snapshot:
        print('Snapshot audit passed for the implemented formalization.')
    else:
        print('Intermediate audit passed. This is not a completed-paper certificate.')


if __name__ == '__main__':
    try:
        main()
    except (RuntimeError, KeyError, ValueError, OSError, subprocess.CalledProcessError) as error:
        print('Audit failed: ' + str(error), file=sys.stderr)
        sys.exit(1)
