import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_torsion_source_exhaustion_gate import build_payload


class SigmaTorsionSourceExhaustionGateTests(unittest.TestCase):
    def test_live_active_branch_has_no_torsion_source(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["torsion_pullback_ready"])
        self.assertTrue(payload["torsion_pullback_zero"])
        self.assertFalse(payload["torsion_source_on_sigma"])
        self.assertFalse(payload["open_torsionful_holst_nieh_yan_sigma"])
        self.assertTrue(payload["archive_torsionful_branch_recommended"])

    def test_spin_or_boundary_source_reopens_torsionful_branch(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            spin = root / "spin.json"
            torsion = root / "torsion.json"
            pullback = root / "pullback.json"
            holst = root / "holst.json"
            theta = root / "theta.json"
            llbrane = root / "llbrane.json"

            spin.write_text(json.dumps({"spin_current_of_a_ready": True}), encoding="utf-8")
            torsion.write_text(
                json.dumps({"closure": {"boundary_torsion_source_of_a_ready": False}}),
                encoding="utf-8",
            )
            pullback.write_text(
                json.dumps(
                    {
                        "Sigma_torsion_pullback_ready": True,
                        "torsion_T_internal_I_ab": [[[0.0]]],
                    }
                ),
                encoding="utf-8",
            )
            holst.write_text(json.dumps({"routes": {}}), encoding="utf-8")
            theta.write_text(json.dumps({"torsionless_pullback": True}), encoding="utf-8")
            llbrane.write_text(json.dumps({"chi_LL_derivation_ready": False}), encoding="utf-8")

            payload = build_payload(spin, torsion, pullback, holst, theta, llbrane)

        self.assertTrue(payload["torsion_source_on_sigma"])
        self.assertTrue(payload["open_torsionful_holst_nieh_yan_sigma"])
        self.assertFalse(payload["archive_torsionful_branch_recommended"])


if __name__ == "__main__":
    unittest.main()
