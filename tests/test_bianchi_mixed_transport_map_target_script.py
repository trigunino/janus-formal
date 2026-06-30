from __future__ import annotations

import unittest

from scripts.build_bianchi_mixed_transport_map_target import build_payload


class BianchiMixedTransportMapTargetTests(unittest.TestCase):
    def test_transport_map_target_is_not_physics_closure(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["physics_closed"])
        self.assertIn("mixed transport maps", payload["verdict"])
        self.assertIn("M_minus_to_plus", " ".join(payload["required_inputs"]))

    def test_forbidden_shortcuts_block_naive_tensor_lensing(self) -> None:
        payload = build_payload()
        forbidden = " ".join(payload["forbidden_shortcuts"])
        residuals = " ".join(payload["residual_hooks"])

        self.assertIn("K_plus=T_minus", forbidden)
        self.assertIn("absorbing Q_cross into Q_det", forbidden)
        self.assertIn("R_plus^mu", residuals)
        self.assertIn("R_minus^mu", residuals)

    def test_qcross_l_map_must_match_bianchi_transport_maps(self) -> None:
        payload = build_payload()
        compatibility = " ".join(payload["compatibility_requirements"])

        self.assertIn("L_minus_to_plus", " ".join(payload["required_inputs"]))
        self.assertIn("M_minus_to_plus", compatibility)
        self.assertIn("K_plus", compatibility)
        self.assertIn("M_plus_to_minus", compatibility)
        self.assertIn("R_plus^mu=0 and R_minus^mu=0", compatibility)


if __name__ == "__main__":
    unittest.main()
