import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_complete_cl_convention_calibration_gate import build_payload as calibration_payload
from scripts.build_p0_eft_janus_z4_complete_gr_reference_convention_handshake_gate import build_payload as handshake_payload


class P0EFTJanusZ4CompleteConventionHandshakeTests(unittest.TestCase):
    def test_calibrated_vector_has_gr_reference_convention_but_no_validation(self):
        calibration = calibration_payload()
        handshake = handshake_payload()

        self.assertTrue(calibration["cl_convention_calibration_passed"])
        self.assertTrue(Path(calibration["calibrated_theory_vector_path"]).exists())
        self.assertEqual(calibration["calibrated_units"], "dimensionless_Cl_CAMB_convention_calibrated")
        self.assertTrue(handshake["gr_reference_convention_handshake_passed"])
        self.assertEqual(handshake["cl_vs_dl_convention"], "C_l")
        self.assertFalse(handshake["observed_planck_validation"])
        self.assertFalse(handshake["candidate_promotion_allowed"])
        self.assertFalse(handshake["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
