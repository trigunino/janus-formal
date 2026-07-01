from __future__ import annotations

import unittest

from scripts.build_p0_eft_janus_z4_tt_swisw_planck_gate import LIKELIHOODS, _info


class P0EFTJanusZ4TTSWISWPlanckGateTests(unittest.TestCase):
    def test_gate_uses_tt_swisw_branch_spectra(self) -> None:
        info = _info(LIKELIHOODS["lowl_TT"])
        theory = info["theory"]["janus_lab.z4_cmb_cobaya.JanusZ4NativeBoltzmann"]

        self.assertIn("tt_swisw_solver_branch_spectra.csv", theory["spectra_path"])
        self.assertFalse("camb" in str(theory["spectra_path"]).lower())


if __name__ == "__main__":
    unittest.main()
