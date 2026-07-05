import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_holst_torsion_flux_zero_or_equivariance_gate import (
    build_payload,
)


def _holst_inputs(values):
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "torsionless_Nieh_Yan_zero_identity_ready": True,
        "E_HolstNiehYan_values": values,
    }


class HolstTorsionFluxZeroOrEquivarianceGateTests(unittest.TestCase):
    def test_torsionless_zero_radial_flux_closes_local_sigma_slot(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "holst_inputs.json"
            path.write_text(json.dumps(_holst_inputs([0.0, 0.0, 0.0])), encoding="utf-8")

            payload = build_payload(input_path=path)

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["routes"]["torsionless_boundary_flux"]["ready"])
        self.assertEqual(payload["scope"]["off_sigma_bulk_Holst_stress"], "not_claimed")

    def test_nonzero_holst_radial_values_keep_gate_blocked(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "holst_inputs.json"
            path.write_text(json.dumps(_holst_inputs([0.0, 1e-3])), encoding="utf-8")

            payload = build_payload(input_path=path)

        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "Holst_boundary_flux_zero_or_Z2_equivariance")


if __name__ == "__main__":
    unittest.main()
