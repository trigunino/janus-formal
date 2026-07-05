import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_signed_cover_time_parity_gate import (
    build_payload,
)


def _input_payload(pullback: str = "minus_self") -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_curvature_fit_used": False,
        "observational_time_gauge_fit_used": False,
        "signed_cover_time_coordinate": {
            "coordinate_defined_on_S4_cover": True,
            "z2_equivariant_time_coordinate_derived": True,
            "flrw_time_gauge_uses_this_coordinate": True,
            "antipodal_pullback": pullback,
        },
    }


class SignedCoverTimeParityGateTests(unittest.TestCase):
    def test_missing_input_blocks_but_rule_ready(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(input_path=Path(tmp) / "missing.json")

        self.assertFalse(payload["gate_passed"])
        self.assertTrue(payload["signed_cover_time_parity_rule_ready"])

    def test_minus_self_writes_odd_time_parity(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            input_path = tmpdir / "signed.json"
            output_path = tmpdir / "parity.json"
            input_path.write_text(json.dumps(_input_payload("minus_self")), encoding="utf-8")

            payload = build_payload(input_path=input_path, output_path=output_path)
            written = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["antipodal_time_parity"], "odd")
        self.assertEqual(
            written["time_coordinate_parity"]["antipodal_time_parity"], "odd"
        )

    def test_plus_self_writes_even_time_parity(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            input_path = tmpdir / "signed.json"
            output_path = tmpdir / "parity.json"
            input_path.write_text(json.dumps(_input_payload("plus_self")), encoding="utf-8")

            payload = build_payload(input_path=input_path, output_path=output_path)
            written = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["antipodal_time_parity"], "even")
        self.assertEqual(
            written["time_coordinate_parity"]["antipodal_time_parity"], "even"
        )

    def test_forbidden_observational_time_gauge_fit_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            input_path = tmpdir / "signed.json"
            payload = _input_payload("minus_self")
            payload["observational_time_gauge_fit_used"] = True
            input_path.write_text(json.dumps(payload), encoding="utf-8")

            result = build_payload(input_path=input_path, output_path=tmpdir / "out.json")

        self.assertFalse(result["gate_passed"])
        self.assertIn("Forbidden provenance", result["validation_error"])


if __name__ == "__main__":
    unittest.main()
