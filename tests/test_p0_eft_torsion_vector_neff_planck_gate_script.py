from __future__ import annotations

import unittest

from scripts.build_p0_eft_torsion_vector_neff_planck_gate import build_payload


class P0EFTTorsionVectorNeffPlanckGateTests(unittest.TestCase):
    def test_torsion_vector_neff_gate_runs(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "torsion-vector-neff-planck-gate-run")
        self.assertTrue(payload["packages_ready"])
        self.assertTrue(payload["fork_ready"])
        self.assertEqual(len(payload["rows"]), 2)

    def test_required_neff_is_not_claimed_as_derived(self) -> None:
        payload = build_payload()

        self.assertGreater(payload["required_nnu_for_bao_rd"], payload["current_nnu"])
        self.assertFalse(payload["is_derived_geometry"])


if __name__ == "__main__":
    unittest.main()
