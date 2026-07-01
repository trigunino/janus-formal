from __future__ import annotations

import unittest

from scripts.build_p0_eft_observational_status_verdict import build_payload


class P0EFTObservationalStatusVerdictTests(unittest.TestCase):
    def test_formal_closure_does_not_imply_observational_pass(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["formal_janus_orbifold_scaffold_closed"])
        self.assertTrue(payload["cmb_simple_branch_excluded_by_planck"])
        self.assertFalse(payload["full_observational_cosmology_passes"])
        self.assertFalse(payload["full_cosmology_prediction_ready_no_fit"])

    def test_next_lock_is_primordial_sector(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["requires_new_coupled_primordial_sector"])
        self.assertTrue(payload["lowe_tau_only_excluded"])


if __name__ == "__main__":
    unittest.main()
