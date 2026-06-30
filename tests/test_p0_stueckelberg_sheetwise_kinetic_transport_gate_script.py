from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_sheetwise_kinetic_transport_gate import (
    build_payload,
    render_markdown,
)


class P0StueckelbergSheetwiseKineticTransportGateTests(unittest.TestCase):
    def test_sheetwise_route_avoids_single_global_phi_l(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "sheetwise-kinetic-route-open")
        self.assertFalse(payload["uses_single_global_phi_l"])
        self.assertTrue(payload["requires_sheetwise_phi_l_or_full_f"])
        self.assertTrue(payload["pre_caustic_single_sheet_recovers_dust"])
        self.assertFalse(payload["sheet_sum_conservation_proved"])
        self.assertFalse(payload["phase_space_measure_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_equations_include_vlasov_sheet_and_moments(self) -> None:
        text = " ".join(build_payload()["equations"])

        self.assertIn("D_t f", text)
        self.assertIn("A^i_Janus", text)
        self.assertIn("sum_s", text)
        self.assertIn("T^{mu nu}", text)
        self.assertIn("Q_cross_total", text)

    def test_forbidden_shortcuts_block_fake_closure(self) -> None:
        text = " ".join(build_payload()["forbidden_shortcuts"])

        self.assertIn("single global phi/L", text)
        self.assertIn("fitted Q_cross", text)
        self.assertIn("Q_ijk=0", text)

    def test_markdown_reports_nonpredictive_route(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Sheetwise Kinetic", markdown)
        self.assertIn("Uses single global phi/L: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
