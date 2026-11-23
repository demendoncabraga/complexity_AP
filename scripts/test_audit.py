"""Regression tests for the coverage and dependency audits."""
import unittest
import json
from pathlib import Path
import tempfile
from unittest.mock import patch
from types import SimpleNamespace
from check_dependencies import check
from audit import axiom_command, authorized_project_axiom, validate_terminal_scope


class AxiomCommandTests(unittest.TestCase):
    def test_public_name_uses_print_axioms(self):
        self.assertEqual(axiom_command('PaperFormalization.result'),
                         '#print axioms PaperFormalization.result')

    def test_private_name_preserves_numeric_component(self):
        command = axiom_command('_private.PaperFormalization.M.0.PaperFormalization.lemma')
        self.assertIn('(Lean.Name.num', command)
        self.assertNotIn('"0"', command)
        self.assertIn('$(Lean.mkIdent name)', command)


class ExternalAxiomTests(unittest.TestCase):
    def test_only_named_enflo_axiom_is_authorized(self):
        path = Path('lean/PaperFormalization/PaperAssumptions.lean')
        self.assertTrue(authorized_project_axiom(path, 'axiom enfloNoAP :'))
        self.assertFalse(authorized_project_axiom(path, 'axiom other :'))
        self.assertFalse(authorized_project_axiom(Path('lean/PaperFormalization/Other.lean'),
                                                  'axiom enfloNoAP :'))
        self.assertFalse(authorized_project_axiom(path, 'axiom enfloNoAP : False'))


class TerminalScopeTests(unittest.TestCase):
    def setUp(self):
        self.coverage = dict(inventory_complete=True, paper_roots=['PaperFormalization.result'])
        self.items = [dict(id='proved', status='verified', declaration='PaperFormalization.result')]

    def test_complete_inventory_accepted(self):
        validate_terminal_scope(self.coverage, self.items)

    def test_incomplete_inventory_rejected(self):
        with self.assertRaises(RuntimeError):
            validate_terminal_scope(dict(self.coverage, inventory_complete=False), self.items)

    def test_empty_inventory_rejected(self):
        with self.assertRaises(RuntimeError):
            validate_terminal_scope(self.coverage, [])

    def test_missing_roots_rejected(self):
        with self.assertRaises(RuntimeError):
            validate_terminal_scope(dict(self.coverage, paper_roots=[]), self.items)

    def test_unverified_entries_rejected(self):
        for status in ['in_progress', 'not_started', 'external_assumption']:
            with self.subTest(status=status), self.assertRaises(RuntimeError):
                validate_terminal_scope(self.coverage, [dict(self.items[0], status=status)])


class DependencyScopeTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / 'lean/PaperFormalization').mkdir(parents=True)
        (self.root / 'lean/PaperFormalization/Final.lean').write_text('-- fixture\n')
        self.index = self.root / '.lake/build/lib/lean/PaperFormalization/Final.ilean'
        self.index.parent.mkdir(parents=True)
        self.data = dict(decls={name: [i, 0, i, 10] for i, name in enumerate(
            ['PaperFormalization.result', 'PaperFormalization.helper', 'PaperFormalization.tacticHelper'])}, references={
                json.dumps(dict(c=dict(m='PaperFormalization.Final', n='PaperFormalization.tacticHelper'))):
                    dict(usages=[[0, 0, 0, 1, 'PaperFormalization.result']])})
        self.kernel = dict(roots=['PaperFormalization.result'], declarations=[
            dict(name='PaperFormalization.result', deps=['PaperFormalization.helper']),
            dict(name='PaperFormalization.helper', deps=[])])
        self.inventory = dict(paper_roots=self.kernel['roots'],
                              items=[dict(declaration=n) for n in self.data['decls']])

    def run_check(self, *, include_deferred=False):
        self.index.write_text(json.dumps(self.data))
        (self.root / 'lean/coverage.json').write_text(json.dumps(self.inventory))
        with patch('check_dependencies.subprocess.run', return_value=SimpleNamespace(
                stdout=json.dumps(self.kernel))), patch('builtins.print'):
            check(self.root, include_deferred=include_deferred)

    def test_kernel_and_tactic_dependencies_retained(self):
        self.run_check()

    def test_unused_declaration_rejected(self):
        self.data['decls']['PaperFormalization.obsolete'] = [9, 0, 9, 10]
        self.inventory['items'].append(dict(declaration='PaperFormalization.obsolete'))
        with self.assertRaisesRegex(RuntimeError, 'outside the final proof'):
            self.run_check()

    def test_missing_inventory_entry_rejected(self):
        self.inventory['items'].pop()
        with self.assertRaisesRegex(RuntimeError, 'Inventory/source mismatch'):
            self.run_check()

    def test_stale_inventory_entry_rejected(self):
        self.inventory['items'].append(dict(declaration='PaperFormalization.removed'))
        with self.assertRaisesRegex(RuntimeError, 'Inventory/source mismatch'):
            self.run_check()

    def test_missing_kernel_source_rejected(self):
        self.kernel['declarations'].append(dict(name='PaperFormalization.missing', deps=[]))
        with self.assertRaisesRegex(RuntimeError, 'no source declaration'):
            self.run_check()

    def test_deferred_support_is_explicit(self):
        helper = 'PaperFormalization.helper'
        self.kernel['deferredSupport'] = [helper]
        self.inventory['deferred_support_roots'] = [helper]
        self.inventory['items'].append(dict(id='deferred_thm', status='in_progress'))
        self.run_check(include_deferred=True)
        with self.assertRaisesRegex(RuntimeError, 'require the snapshot audit'):
            self.run_check()

    def test_undeclared_deferred_support_is_rejected(self):
        self.kernel['deferredSupport'] = ['PaperFormalization.helper']
        with self.assertRaisesRegex(RuntimeError, 'Deferred support roots differ'):
            self.run_check(include_deferred=True)

    def test_wrong_roots_rejected(self):
        self.inventory['paper_roots'] = ['PaperFormalization.wrong']
        with self.assertRaisesRegex(RuntimeError, 'Paper roots differ'):
            self.run_check()


if __name__ == '__main__':
    unittest.main()
