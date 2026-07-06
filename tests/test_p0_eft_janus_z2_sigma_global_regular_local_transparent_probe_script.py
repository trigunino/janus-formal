import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_global_regular_local_transparent_probe import (
    build_payload,
)


class JanusZ2SigmaGlobalRegularLocalTransparentProbeTest(unittest.TestCase):
    def test_probe_is_diagnostic_and_does_not_select_ratio(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            payload = build_payload(
                primitive_path=tmpdir / "primitive.json",
                component_path=tmpdir / "component.json",
            )
        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["diagnostic_only"])
        self.assertFalse(payload["writes_active_manifest"])
        self.assertTrue(payload["all_defects_zero_on_grid"])
        self.assertFalse(payload["R_Sigma_over_ell_collar_selected"])
        self.assertEqual(
            payload["primary_blocker"],
            "global_nonlocal_defect_needed_for_radius_selection",
        )


if __name__ == "__main__":
    unittest.main()
