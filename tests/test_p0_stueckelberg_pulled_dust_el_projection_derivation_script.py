from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_pulled_dust_el_projection_derivation import build_payload


class P0PulledDustELProjectionDerivationTests(unittest.TestCase):
    def test_derivation_is_open_not_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "pulled-dust-el-projection-open")
        self.assertFalse(payload["projected_el_source_derived"])
        self.assertFalse(payload["measure_terms_closed"])
        self.assertFalse(payload["dl_terms_closed"])
        self.assertFalse(payload["mirror_inverse_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_chain_contains_action_variations_projection_and_mirror(self) -> None:
        chain = " ".join(row["identity"] for row in build_payload()["derivation_chain"])

        self.assertIn("S_dust", chain)
        self.assertIn("delta(B rho)", chain)
        self.assertIn("delta_L u", chain)
        self.assertIn("h E_{Phi,L} = rho h C(u,u)", chain)
        self.assertIn("inverse Phi/L", chain)

    def test_acceptance_checks_forbid_axiom_or_multiplier_shortcut(self) -> None:
        checks = " ".join(build_payload()["acceptance_checks"])

        self.assertIn("pulled dust action", checks)
        self.assertIn("transverse projector h", checks)
        self.assertIn("rho h Cuu", checks)
        self.assertIn("no transverse multiplier", checks)
        self.assertIn("no weak-congruence axiom", checks)


if __name__ == "__main__":
    unittest.main()
