import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_global_twist_holonomy_probe import build_payload


class JanusZ2SigmaGlobalTwistHolonomyProbeTest(unittest.TestCase):
    def test_twist_probe_selects_ratio_but_remains_diagnostic(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            payload = build_payload(
                primitive_path=tmpdir / "primitive.json",
                component_path=tmpdir / "component.json",
            )
        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["diagnostic_only"])
        self.assertFalse(payload["writes_active_manifest"])
        self.assertFalse(payload["twist_model_source_derived"])
        self.assertTrue(payload["R_Sigma_over_ell_collar_selected"])
        self.assertEqual(payload["regularity_roots"], [1.0])
        self.assertEqual(
            payload["primary_blocker"],
            "derive_projective_holonomy_twist_from_active_collar_geometry",
        )


if __name__ == "__main__":
    unittest.main()
