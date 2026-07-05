import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_time_gauge_leaf_action_input_writer_gate import (
    build_payload,
)


def _input_payload(parity: str = "odd") -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_curvature_fit_used": False,
        "observational_time_gauge_fit_used": False,
        "time_coordinate_parity": {
            "z2_equivariant_time_coordinate_derived": True,
            "antipodal_time_parity": parity,
        },
    }


class TimeGaugeLeafActionInputWriterGateTests(unittest.TestCase):
    def test_missing_input_blocks_but_rule_ready(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(input_path=Path(tmp) / "missing.json")

        self.assertFalse(payload["gate_passed"])
        self.assertTrue(payload["time_parity_to_leaf_action_rule_ready"])

    def test_even_time_parity_writes_invariant_leaf_action(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            input_path = tmpdir / "time.json"
            output_path = tmpdir / "leaf.json"
            input_path.write_text(json.dumps(_input_payload("even")), encoding="utf-8")

            payload = build_payload(input_path=input_path, output_path=output_path)
            written = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["leaf_action_type"], "antipodal_invariant_leaf")
        self.assertEqual(
            written["time_gauge_leaf_action"]["leaf_action_type"],
            "antipodal_invariant_leaf",
        )

    def test_odd_time_parity_writes_paired_leaf_action(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            input_path = tmpdir / "time.json"
            output_path = tmpdir / "leaf.json"
            input_path.write_text(json.dumps(_input_payload("odd")), encoding="utf-8")

            payload = build_payload(input_path=input_path, output_path=output_path)
            written = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["leaf_action_type"], "antipodal_paired_leaves")
        self.assertEqual(
            written["time_gauge_leaf_action"]["leaf_action_type"],
            "antipodal_paired_leaves",
        )

    def test_forbidden_time_gauge_fit_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            input_path = tmpdir / "time.json"
            payload = _input_payload("odd")
            payload["observational_time_gauge_fit_used"] = True
            input_path.write_text(json.dumps(payload), encoding="utf-8")

            result = build_payload(input_path=input_path, output_path=tmpdir / "out.json")

        self.assertFalse(result["gate_passed"])
        self.assertIn("Forbidden provenance", result["validation_error"])


if __name__ == "__main__":
    unittest.main()
