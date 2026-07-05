import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_rsigma_certificate_payload_input_writer_gate import (
    build_payload,
)


def _term() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "term_name": "E_HolstNiehYan",
        "a_grid": [0.5, 1.0],
        "term_values": [-1.0, -2.0],
        "term_provenance": "active Holst Nieh Yan radial block",
    }


def _scalar(key: str, value: float) -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "scalars": {key: value},
    }


class RSigmaCertificatePayloadInputWriterGateTests(unittest.TestCase):
    def test_writes_payload_from_active_inputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            term = root / "term.json"
            h0 = root / "h0.json"
            radius = root / "radius.json"
            sign = root / "sign.json"
            out = root / "payload.json"
            term.write_text(json.dumps(_term()), encoding="utf-8")
            h0.write_text(json.dumps(_scalar("H0_Z2Sigma_km_s_Mpc", 70.0)), encoding="utf-8")
            radius.write_text(json.dumps(_scalar("R_curv_Z2Sigma_Mpc", 3000.0)), encoding="utf-8")
            sign.write_text(
                json.dumps({"active_core": "Z2_tunnel_Sigma", "scalars": {"k_Z2Sigma": 1}}),
                encoding="utf-8",
            )

            payload = build_payload(
                term_grid_path=term,
                h0_input_path=h0,
                radius_input_path=radius,
                curvature_sign_path=sign,
                output_path=out,
            )
            written = json.loads(out.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(written["a_grid"], [0.5, 1.0])
        self.assertEqual(written["z2_orientation_sign"], -1.0)
        self.assertEqual(written["R_curv_Z2Sigma_Mpc"], 3000.0)

    def test_missing_inputs_block(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(term_grid_path=Path(tmp) / "missing.json")

        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "rsigma_certificate_payload_inputs")


if __name__ == "__main__":
    unittest.main()
