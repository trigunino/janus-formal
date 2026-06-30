from __future__ import annotations

import unittest

from scripts.build_p0_linear_imatter_tensor_contract import build_payload


class P0LinearImatterTensorContractTests(unittest.TestCase):
    def test_contract_defined_but_variations_open(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "tensor-contract-defined-variation-open")
        self.assertTrue(payload["imatter_tensor_contract_defined"])
        self.assertTrue(payload["dust_projection_bridge_available"])
        self.assertTrue(payload["metric_measure_variation_available"])
        self.assertFalse(payload["metric_variation_closed"])
        self.assertTrue(payload["l_variation_algebra_closed"])
        self.assertTrue(payload["lorentz_projected_e_l_closed"])
        self.assertFalse(payload["map_l_variation_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_contracts_cover_plus_minus_and_dust_limit(self) -> None:
        text = " ".join(row["formula"] for row in build_payload()["contracts"])

        self.assertIn("I_matter_plus", text)
        self.assertIn("L T_minus L^T", text)
        self.assertIn("I_matter_minus", text)
        self.assertIn("L^{-1} T_plus L^{-T}", text)
        self.assertIn("rho_plus rho_minus", text)
        self.assertIn("u_plus.u_minus_to_plus", text)

    def test_variation_requirements_keep_metric_l_phi_and_pressure_explicit(self) -> None:
        reqs = " ".join(build_payload()["variation_requirements"])

        self.assertIn("metric variation", reqs)
        self.assertIn("volume-measure trace", reqs)
        self.assertIn("L variation", reqs)
        self.assertIn("phi variation", reqs)
        self.assertIn("pressure/Pi", reqs)


if __name__ == "__main__":
    unittest.main()
