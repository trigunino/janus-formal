from __future__ import annotations

import unittest

from scripts.build_p0_dlogb4vol_measure_law_derivation_attempt import build_payload


class P0DlogB4volMeasureLawDerivationAttemptTests(unittest.TestCase):
    def test_attempt_is_bounded_and_open(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "derivation-attempt-open")
        self.assertTrue(payload["b4vol_separated_from_v3_dust"])
        self.assertTrue(payload["rho_to_separated_from_measure"])
        self.assertTrue(payload["product_rule_targets_written"])
        self.assertTrue(payload["residual_substitution_written"])
        self.assertFalse(payload["source_identities_supplied"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_measure_conventions_separate_4volume_3volume_and_density(self) -> None:
        rows = {row["name"]: row for row in build_payload()["measure_conventions"]}

        self.assertIn("B_4vol", rows)
        self.assertIn("V3_dust", rows)
        self.assertIn("rho_to", rows)
        self.assertIn("lapse ratio", rows["B_4vol"]["contains"])
        self.assertIn("spatial volume only", rows["V3_dust"]["contains"])
        self.assertIn("matter density", rows["rho_to"]["contains"])

    def test_product_rule_targets_cover_both_receivers_and_substitution(self) -> None:
        rows = build_payload()["product_rule_targets"]
        receivers = {row["receiver"] for row in rows}
        text = " ".join(row["target"] + " " + row["expanded"] + " " + row["residual_substitution"] for row in rows)

        self.assertEqual(receivers, {"plus", "minus"})
        self.assertIn("D_plus_nu(B_4vol_plus_from_minus rho_minus_to_plus", text)
        self.assertIn("D_minus_nu(B_4vol_minus_from_plus rho_plus_to_minus", text)
        self.assertIn("D_plus_nu log(B_4vol_plus_from_minus)", text)
        self.assertIn("D_minus_nu log(B_4vol_minus_from_plus)", text)
        self.assertIn("-> -rho_minus_to_plus", text)
        self.assertIn("-> -rho_plus_to_minus", text)
        self.assertTrue(all(not row["closed"] for row in rows))

    def test_required_identities_include_source_slice_lapse_and_transport_laws(self) -> None:
        identities = " ".join(build_payload()["required_identities"])

        self.assertIn("source identity", identities)
        self.assertIn("log N_source", identities)
        self.assertIn("log gamma_source", identities)
        self.assertIn("slice-to-4D lapse reinsertion", identities)
        self.assertIn("transported density law", identities)
        self.assertIn("transported velocity/tetrad law", identities)
        self.assertIn("mirror consistency", identities)

    def test_forbids_qdet_qcross_absorption_and_double_counting(self) -> None:
        payload = build_payload()
        forbidden = " ".join(payload["forbidden_operations"])

        self.assertTrue(payload["qdet_qcross_scalar_absorption_forbidden"])
        self.assertTrue(payload["double_counting_forbidden"])
        self.assertIn("absorb D log B_4vol into Q_det", forbidden)
        self.assertIn("absorb D log B_4vol into Q_cross", forbidden)
        self.assertIn("already been included", forbidden)
        self.assertIn("Count".lower(), forbidden.lower())
        self.assertIn("pure 3-volume dust law", forbidden)


if __name__ == "__main__":
    unittest.main()
