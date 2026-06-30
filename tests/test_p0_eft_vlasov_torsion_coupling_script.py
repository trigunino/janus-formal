from __future__ import annotations

import unittest

from scripts.build_p0_eft_vlasov_torsion_coupling import build_payload


class P0EFTVlasovTorsionCouplingTests(unittest.TestCase):
    def test_spinless_torsion_force_zero_but_spinning_open(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["spinless_vlasov_torsion_force_closed_zero"])
        self.assertFalse(status["spinning_vlasov_torsion_force_derived"])
        self.assertFalse(status["lensing_growth_sources_closed"])


if __name__ == "__main__":
    unittest.main()
