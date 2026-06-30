from __future__ import annotations

import unittest

from scripts.build_bianchi_anisotropic_stress_transport_target import build_payload


class BianchiAnisotropicStressTransportTargetTests(unittest.TestCase):
    def test_anisotropic_stress_is_tensor_target_not_closure(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "tensor-target")
        self.assertFalse(payload["physics_closed"])
        self.assertIn("Pi_s^{mu nu}", " ".join(payload["tensor_form"]))

    def test_transport_targets_keep_both_bianchi_residuals(self) -> None:
        targets = " ".join(build_payload()["transport_targets"])

        self.assertIn("D_plus_nu", targets)
        self.assertIn("D_minus_nu", targets)
        self.assertIn("K_plus", targets)
        self.assertIn("K_minus", targets)

    def test_forbidden_reductions_block_scalar_shortcut(self) -> None:
        forbidden = " ".join(build_payload()["forbidden_reductions"])

        self.assertIn("replace Pi_s^{mu nu} by scalar rho_s", forbidden)
        self.assertIn("reuse perfect-fluid w_cross branch", forbidden)
        self.assertIn("merge anisotropic stress into Q_cross", forbidden)


if __name__ == "__main__":
    unittest.main()
