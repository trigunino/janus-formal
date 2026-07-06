import json
import tempfile
import unittest
from pathlib import Path

from scripts.write_p0_eft_janus_z2_sigma_rsigma_over_ell_collar_from_projective_stereographic import (
    build_payload,
)


class JanusZ2SigmaRSigmaOverEllFromProjectiveStereographicScriptTest(unittest.TestCase):
    def test_writes_ratio_but_not_absolute_radius_certificate(self):
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp) / "ratio.json"
            payload = build_payload(output_path=output)
            manifest = json.loads(output.read_text(encoding="utf-8"))

        self.assertTrue(payload["output_written"])
        self.assertEqual(payload["R_Sigma_over_ell_collar"], 1.0)
        self.assertTrue(payload["ratio_solution_ready"])
        self.assertFalse(payload["full_R_Sigma_solution_certificate_ready"])
        self.assertEqual(payload["primary_blocker"], "absolute_ell_collar_scale_not_fixed")
        self.assertEqual(manifest["R_Sigma_over_ell_collar"], 1.0)
        self.assertFalse(manifest["absolute_ell_collar_fixed"])


if __name__ == "__main__":
    unittest.main()
