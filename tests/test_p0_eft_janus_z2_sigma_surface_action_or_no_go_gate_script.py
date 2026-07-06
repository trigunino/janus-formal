from __future__ import annotations

import unittest

from scripts.derive_p0_eft_janus_z2_sigma_surface_action_or_no_go_gate import (
    build_payload,
)


class SurfaceActionOrNoGoGateTests(unittest.TestCase):
    def test_current_no_extension_inputs_underselect_surface_action(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["no_extension_inputs"]["mpla_local_throat"])
        self.assertTrue(payload["no_extension_inputs"]["projective_ratio"])
        self.assertTrue(payload["no_extension_inputs"]["souriau_global_charge"])
        self.assertFalse(payload["no_extension_inputs"]["souriau_local_density"])
        self.assertFalse(payload["E_counterterm_closed"])
        self.assertFalse(payload["sigma_alpha_h_closed"])
        self.assertFalse(payload["full_no_fit_prediction_ready"])
        self.assertTrue(
            payload["no_extension_inputs"][
                "first_order_boundary_topological_density_eliminated"
            ]
        )
        self.assertEqual(
            payload["decision"],
            "first_order_boundary_sources_eliminated_but_cross_or_corner_source_open",
        )
        self.assertIn(
            "Holst/Palatini theta non-GHY trace channel",
            payload["eliminated_surface_density_sources"],
        )

    def test_forbidden_shortcuts_are_explicit(self) -> None:
        payload = build_payload()

        self.assertIn("set E_counterterm = 0 by assumption", payload["forbidden_shortcuts"])
        self.assertIn(
            "differentiate Souriau global charge as local density",
            payload["forbidden_shortcuts"],
        )
        self.assertIn("fit a0..a3 observationally", payload["forbidden_shortcuts"])


if __name__ == "__main__":
    unittest.main()
