import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_alpha_branch_archive_readiness_gate import build_payload


class AlphaBranchArchiveReadinessGateTests(unittest.TestCase):
    def test_live_branch_is_archive_ready(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["alpha_generated_no_fit"])
        self.assertTrue(payload["published_janus_equivalence_on_alpha"])
        self.assertFalse(payload["any_reopen_route_ready"])
        self.assertTrue(payload["archive_branch_recommended"])

    def test_nonzero_kks_or_valpha_reopens_branch(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            theta = root / "theta.json"
            souriau = root / "souriau.json"
            llbrane = root / "llbrane.json"
            scouple = root / "scouple.json"
            hard = root / "hard.json"
            theta.write_text(
                json.dumps(
                    {
                        "R_h_trace_values_ready": True,
                        "R_K_trace_values_ready": True,
                        "R_h_trace_values": [0.0],
                        "R_K_trace_values": [0.0],
                    }
                ),
                encoding="utf-8",
            )
            souriau.write_text(
                json.dumps({"local_density_from_charge_available": True}),
                encoding="utf-8",
            )
            llbrane.write_text(json.dumps({"chi_LL_derivation_ready": False}), encoding="utf-8")
            scouple.write_text(
                json.dumps({"m15_action_accepted_for_field_equations": True}),
                encoding="utf-8",
            )
            hard.write_text(
                json.dumps({"valpha_route": {"V_alpha_ready": True}}),
                encoding="utf-8",
            )

            payload = build_payload(theta, souriau, llbrane, scouple, hard)

        self.assertTrue(payload["any_reopen_route_ready"])
        self.assertFalse(payload["archive_branch_recommended"])
        self.assertTrue(
            payload["reopen_routes"]["nonzero_PT_KKS_Souriau_boundary_density"]["ready"]
        )
        self.assertTrue(
            payload["reopen_routes"][
                "published_minisuperspace_action_with_finite_noncompact_orbit_boundary"
            ]["ready"]
        )


if __name__ == "__main__":
    unittest.main()
