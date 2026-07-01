from __future__ import annotations

import unittest

from scripts.run_p0_eft_coherent_primordial_immirzi_planck_gate import build_payload


class P0EFTCoherentPrimordialImmirziPlanckGateTests(unittest.TestCase):
    def test_dry_payload_uses_geometric_delta_i(self) -> None:
        payload = build_payload(execute=False)

        self.assertEqual(payload["status"], "coherent-primordial-immirzi-planck-gate-dry")
        self.assertAlmostEqual(payload["c_coherent_immirzi"], 0.09778424139658529)
        self.assertFalse(payload["full_cosmology_prediction_ready_no_fit"])


if __name__ == "__main__":
    unittest.main()
