from __future__ import annotations

import unittest

from scripts.build_p0_janus_transport_residual_derivation import build_payload


class P0JanusTransportResidualDerivationTests(unittest.TestCase):
    def test_reduces_bianchi_but_keeps_prediction_closed(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["janus_bianchi_reduction_done"])
        self.assertTrue(payload["single_l_structure_required"])
        self.assertTrue(payload["k_and_qcross_linked"])
        self.assertTrue(payload["dust_residual_reduction_done"])
        self.assertFalse(payload["source_equations_inserted"])
        self.assertFalse(payload["r_plus_closed"])
        self.assertFalse(payload["r_minus_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_starts_from_two_janus_bianchi_residuals(self) -> None:
        start = " ".join(build_payload()["janus_bianchi_start"])

        self.assertIn("G_plus", start)
        self.assertIn("G_minus", start)
        self.assertIn("R_plus^mu", start)
        self.assertIn("R_minus^mu", start)

    def test_one_l_structure_induces_k_and_qcross(self) -> None:
        payload = build_payload()
        l_defs = " ".join(payload["l_transport_definition"])
        k_defs = " ".join(payload["induced_k_definition"])
        q_defs = " ".join(payload["qcross_definition"])

        self.assertIn("L_minus_to_plus^T eta L_minus_to_plus=eta", l_defs)
        self.assertIn("K_plus", k_defs)
        self.assertIn("K_minus", k_defs)
        self.assertIn("same L maps", q_defs)
        self.assertIn("Q_cross_plus", q_defs)

    def test_residual_reduction_has_plus_minus_rows_and_dl_terms(self) -> None:
        rows = {row["sector"]: row for row in build_payload()["residual_reduction"]}
        plus_text = " ".join(rows["plus"]["vanishes_if"])
        minus_text = " ".join(rows["minus"]["vanishes_if"])

        self.assertIn("R_plus^A", rows["plus"]["residual"])
        self.assertIn("R_minus^A", rows["minus"]["residual"])
        self.assertIn("D L_minus_to_plus", plus_text)
        self.assertIn("D L_plus_to_minus", minus_text)

    def test_open_items_are_source_equations_not_scalar_patches(self) -> None:
        payload = build_payload()
        needed = " ".join(payload["source_equations_needed"])
        closed_now = " ".join(payload["closed_now"])
        still_open = " ".join(payload["still_open"])

        self.assertIn("D_alpha L_minus_to_plus", needed)
        self.assertIn("same L as the stress transport", needed)
        self.assertIn("scalar Q_det/Q_cross absorption is excluded", closed_now)
        self.assertIn("no prediction", still_open)


if __name__ == "__main__":
    unittest.main()
