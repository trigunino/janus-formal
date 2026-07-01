from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_primordial_imprint_lock import build_payload, write_reports


class P0EFTJanusZ4PrimordialImprintLockTests(unittest.TestCase):
    def test_lock_blocks_planck_until_all_derived_blocks_exist(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-primordial-imprint-lock")
        self.assertTrue(payload["planck_gate_allowed"])
        self.assertFalse(payload["compressed_lcdm_parameters_allowed"])
        self.assertFalse(payload["proxy_visibility_allowed"])
        self.assertFalse(payload["proxy_lensing_allowed"])
        self.assertTrue(payload["official_planck_ready_requires_all_blocks"])
        self.assertTrue(payload["ready_for_planck"])
        self.assertTrue(payload["block_status"]["tt_swisw"])
        self.assertTrue(payload["block_status"]["theta2_visibility"])
        self.assertTrue(payload["block_status"]["weyl_lensing"])
        self.assertTrue(payload["block_status"]["membrane_projection"])
        self.assertTrue(payload["block_status"]["polarization_action"])
        self.assertEqual(payload["evidence"]["upstream_polarization_coefficients"]["c_q"], "1")
        self.assertEqual(payload["evidence"]["upstream_polarization_coefficients"]["c_v"], "0")
        self.assertEqual(payload["evidence"]["upstream_polarization_coefficients"]["c_z4"], "0")
        self.assertEqual(payload["evidence"]["membrane_projection"]["a_sigma"], "2/3")
        self.assertEqual(payload["evidence"]["membrane_projection"]["z4_generator_angle"], "pi/2")
        self.assertEqual(
            payload["execution_order"],
            ["tt_swisw", "polarization_visibility", "weyl_lensing", "official_planck_gate"],
        )

    def test_report_writer_exports_outputs(self) -> None:
        write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_primordial_imprint_lock.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_primordial_imprint_lock.md").exists())


if __name__ == "__main__":
    unittest.main()
