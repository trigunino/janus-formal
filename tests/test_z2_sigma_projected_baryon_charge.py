import unittest

from src.janus_lab.z2_sigma_projected_baryon_charge import (
    validate_active_projected_baryon_charge_payload,
)


def _payload(provenance: str = "active_noether_charge") -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_rd_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_baryon_fit_used": False,
        "normalizations": {
            "projected_baryon_number_charge_Z2Sigma": 12.0,
        },
        "normalization_provenance": {
            "projected_baryon_number_charge_Z2Sigma": provenance,
        },
    }


class Z2SigmaProjectedBaryonChargeTests(unittest.TestCase):
    def test_valid_active_charge_payload_is_canonicalized(self):
        payload = validate_active_projected_baryon_charge_payload(_payload())

        self.assertEqual(
            payload["normalizations"]["projected_baryon_number_charge_Z2Sigma"],
            12.0,
        )
        self.assertFalse(payload["observational_baryon_fit_used"])

    def test_planck_or_fit_provenance_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "Forbidden projected baryon charge provenance"):
            validate_active_projected_baryon_charge_payload(_payload("Planck_LCDM_fit"))

    def test_observational_fit_flag_must_be_false(self):
        payload = _payload()
        payload["observational_baryon_fit_used"] = True

        with self.assertRaisesRegex(ValueError, "observational_baryon_fit_used"):
            validate_active_projected_baryon_charge_payload(payload)


if __name__ == "__main__":
    unittest.main()
