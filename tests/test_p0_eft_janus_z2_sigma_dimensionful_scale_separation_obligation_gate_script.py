import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_dimensionful_scale_separation_obligation_gate import (
    build_payload,
)


def _scale(path: Path) -> None:
    path.write_text(
        json.dumps(
            {
                "active_core": "Z2_tunnel_Sigma",
                "source": "active_derived",
                "scalars": {"h0_R_curv_over_c_Z2Sigma": 7.0},
            }
        ),
        encoding="utf-8",
    )


class DimensionfulScaleSeparationObligationGateTests(unittest.TestCase):
    def test_dimensionless_product_cannot_be_inverted(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            scale = root / "scale.json"
            _scale(scale)

            payload = build_payload(
                scale_path=scale,
                h0_path=root / "missing_h0.json",
                radius_path=root / "missing_radius.json",
            )

        self.assertTrue(payload["dimensionless_scale_exists"])
        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["can_invert_product_to_H0_or_R_curv"])
        self.assertTrue(payload["dimensionless_product_insufficient_for_physical_volume"])
        self.assertTrue(payload["dimensionless_product_insufficient_for_Gamma_drag_over_H0"])

    def test_separate_h0_and_radius_inputs_clear_obligation(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            scale = root / "scale.json"
            h0 = root / "h0.json"
            radius = root / "radius.json"
            _scale(scale)
            h0.write_text("{}", encoding="utf-8")
            radius.write_text("{}", encoding="utf-8")

            payload = build_payload(scale_path=scale, h0_path=h0, radius_path=radius)

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["dimensionful_scale_inputs_ready"])
        self.assertFalse(payload["can_invert_product_to_H0_or_R_curv"])


if __name__ == "__main__":
    unittest.main()
