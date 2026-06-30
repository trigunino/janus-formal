from __future__ import annotations

import unittest

from scripts.build_p0_eft_effective_vlasov_transport_target import build_payload, render_markdown


class P0EFTEffectiveVlasovTransportTargetTests(unittest.TestCase):
    def test_vlasov_per_sheet_is_derived_but_bridge_open(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["vlasov_equation_derived_per_sheet"])
        self.assertTrue(status["bridge_transport_form_written"])
        self.assertTrue(status["phase_space_jacobian_defined"])
        self.assertFalse(status["same_L_bridge_exact"])
        self.assertFalse(status["phase_space_measure_closed"])

    def test_hamiltonian_and_liouville_are_named(self) -> None:
        vlasov = build_payload()["vlasov"]

        self.assertIn("g_s", vlasov["sheet_hamiltonian"])
        self.assertIn("L_s f_s", vlasov["collisionless_equation"])

    def test_bridge_dependency_is_explicit(self) -> None:
        bridge = build_payload()["bridge_transport"]

        self.assertIn("same-L", bridge["bridge_map"])
        self.assertIn("exact Phi", bridge["open_dependency"])

    def test_markdown_keeps_prediction_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("same_L_bridge_exact: False", markdown)
        self.assertIn("prediction_ready_unconditional: False", markdown)


if __name__ == "__main__":
    unittest.main()
