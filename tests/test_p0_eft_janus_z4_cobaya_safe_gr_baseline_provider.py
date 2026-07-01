from __future__ import annotations

import unittest

from janus_lab.z4_cmb_cobaya import DEFAULT_SPECTRA, JanusZ4NativeBoltzmann


class P0EFTJanusZ4CobayaSafeGRBaselineProviderTests(unittest.TestCase):
    def test_default_provider_uses_camb_gr_baseline_without_internal_calibration(self) -> None:
        provider = JanusZ4NativeBoltzmann()
        provider.initialize()
        cls = provider.get_Cl(units="FIRASmuK2")

        self.assertIn("camb_gr_baseline", str(DEFAULT_SPECTRA))
        self.assertFalse(provider.calibrate_internal_units)
        self.assertGreater(len(cls["ell"]), 2500)
        self.assertTrue((cls["tt"][2:] >= 0.0).all())
        self.assertTrue((cls["ee"][2:] >= 0.0).all())


if __name__ == "__main__":
    unittest.main()
