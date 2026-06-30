from __future__ import annotations

import unittest

from scripts.build_p0_cuu_inverse_map_integrability_target import build_payload, render_markdown


class P0CuuInverseMapIntegrabilityTargetTests(unittest.TestCase):
    def test_target_is_open_but_writes_physical_identities(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "cuu-inverse-map-integrability-target-open")
        self.assertTrue(payload["single_cross_dust_bridge_closed"])
        self.assertTrue(payload["inverse_c_relation_written"])
        self.assertTrue(payload["jacobian_from_same_l_written"])
        self.assertTrue(payload["jacobian_curl_numeric_probe_available"])
        self.assertTrue(payload["compatible_jacobian_curl_closes"])
        self.assertFalse(payload["curl_defected_jacobian_curl_closes"])
        self.assertFalse(payload["mirror_inverse_closed"])
        self.assertFalse(payload["integrability_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_identities_cover_inverse_c_and_phi_integrability(self) -> None:
        payload = build_payload()
        formulas = " ".join(row["formula"] for row in payload["identities"])

        self.assertIn("C_minus", formulas)
        self.assertIn("C_plus", formulas)
        self.assertIn("J^mu_a", formulas)
        self.assertIn("partial_[a J^mu_b]", formulas)
        self.assertIn("numeric dJ=0", formulas)
        self.assertTrue(any(row["name"] == "inverse_connection_difference" for row in payload["identities"]))
        self.assertTrue(any(row["name"] == "phi_integrability" for row in payload["identities"]))
        self.assertTrue(any(row["name"] == "jacobian_curl_numeric_gate" for row in payload["identities"]))

    def test_forbids_independent_mirror_and_pointwise_l_promotion(self) -> None:
        text = " ".join(build_payload()["forbidden_shortcuts"])

        self.assertIn("independent plus/minus C", text)
        self.assertIn("pointwise L", text)
        self.assertIn("Jacobian curl test", text)
        self.assertIn("pressure/Pi", text)

    def test_markdown_keeps_prediction_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Prediction ready: False", markdown)
        self.assertIn("C_minus", markdown)
        self.assertIn("partial_[a J^mu_b]", markdown)
        self.assertIn("Compatible Jacobian curl closes: True", markdown)


if __name__ == "__main__":
    unittest.main()
