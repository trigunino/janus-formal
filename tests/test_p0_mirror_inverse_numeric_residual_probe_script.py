from __future__ import annotations

import unittest

import numpy as np
from scipy import linalg

from scripts.build_p0_mirror_inverse_numeric_residual_probe import (
    build_payload,
    consistency_blocks,
    pack_state,
    reference_l_pm,
    render_markdown,
    summarize_block,
)


class P0MirrorInverseNumericResidualProbeTests(unittest.TestCase):
    def test_probe_is_bounded_numeric_only_after_integrability(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "numeric-residual-probe-only")
        self.assertIn("p0_bianchi_minimal_curvature_integrability_system", payload["depends_on"])
        self.assertIn("p0_bianchi_minimal_mirror_inverse_attempt", payload["depends_on"])
        self.assertIn("numpy", payload["tooling"])
        self.assertIn("scipy.linalg", payload["tooling"])
        self.assertTrue(payload["bounded_numeric_artifact"])
        self.assertFalse(payload["uses_fit"])
        self.assertFalse(payload["scalar_absorption_allowed"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_compatible_and_inconsistent_mirrored_rows_are_distinguished(self) -> None:
        payload = build_payload()
        compatible = payload["compatible_probe"]
        inconsistent = payload["inconsistent_rows_probe"]

        self.assertTrue(payload["compatible_mirrored_rows_close"])
        self.assertFalse(payload["inconsistent_mirrored_rows_close"])
        self.assertLess(compatible["residual_norm"], 1e-10)
        self.assertGreater(inconsistent["residual_norm"], 1e-3)
        self.assertTrue(inconsistent["inverse_l_closes"])
        self.assertTrue(inconsistent["reciprocal_b4vol_closes"])

    def test_consistency_blocks_encode_mirror_rows_inverse_l_and_reciprocal_b(self) -> None:
        l_pm = reference_l_pm()
        l_mp = linalg.inv(l_pm)
        blocks = {block["name"]: block for block in consistency_blocks(l_pm)}

        self.assertEqual(set(blocks), {
            "R_mp_plus_L_mp_R_pm",
            "R_pm_plus_L_pm_R_mp",
            "inverse_L_mp",
            "reciprocal_B_4vol",
        })
        np.testing.assert_allclose(blocks["R_mp_plus_L_mp_R_pm"]["matrix"][:, 0:2], l_mp)
        np.testing.assert_allclose(blocks["R_pm_plus_L_pm_R_mp"]["matrix"][:, 2:4], l_pm)
        np.testing.assert_allclose(blocks["inverse_L_mp"]["rhs"], l_mp.reshape(-1))
        np.testing.assert_allclose(blocks["reciprocal_B_4vol"]["matrix"][0, 8:10], [1.0, 1.0])

    def test_no_scalar_absorption_hides_row_mismatch(self) -> None:
        l_pm = reference_l_pm()
        l_mp = linalg.inv(l_pm)
        state = pack_state(
            r_pm=np.array([0.3, -0.6]),
            r_mp=np.array([-0.15, 0.4]),
            l_mp=l_mp,
            log_b_pm=float(np.log(1.2)),
            log_b_mp=float(-np.log(1.2)),
        )
        row_block = consistency_blocks(l_pm)[0]
        b_block = consistency_blocks(l_pm)[3]

        row_summary = summarize_block(row_block, state)
        b_summary = summarize_block(b_block, state)

        self.assertFalse(row_summary["closed_at_tolerance"])
        self.assertTrue(b_summary["closed_at_tolerance"])
        self.assertGreater(row_summary["residual_norm"], 1e-3)

    def test_markdown_renders_nonpredictive_status(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Compatible mirrored rows close: True", markdown)
        self.assertIn("Inconsistent mirrored rows close: False", markdown)
        self.assertIn("Uses fit: False", markdown)
        self.assertIn("Scalar absorption allowed: False", markdown)
        self.assertIn("Physics closed: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
