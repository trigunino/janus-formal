from __future__ import annotations

import unittest

from scripts.build_p0_eft_janus_z4_integrated_negative_imprint_planck_gate import LIKELIHOODS, _base_info


class P0EFTJanusZ4IntegratedNegativeImprintPlanckGateTests(unittest.TestCase):
    def test_gate_uses_integrated_branch_spectra_path(self) -> None:
        info = _base_info(LIKELIHOODS["lowl_TT"])
        theory = info["theory"]["janus_lab.z4_cmb_cobaya.JanusZ4NativeBoltzmann"]

        self.assertIn("integrated_negative_imprint_branch_spectra.csv", theory["spectra_path"])
        self.assertFalse("camb" in str(theory["spectra_path"]).lower())
        self.assertFalse(info.get("compressed_lcdm_parameters_used", False))


if __name__ == "__main__":
    unittest.main()
