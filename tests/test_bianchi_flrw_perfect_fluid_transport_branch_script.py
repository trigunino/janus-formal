from __future__ import annotations

import unittest

import sympy as sp

from scripts.build_bianchi_flrw_perfect_fluid_transport_branch import build_payload


class BianchiFlrwPerfectFluidTransportBranchTests(unittest.TestCase):
    def test_branch_requires_declared_cross_equation_of_state(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["branch_closed"])
        self.assertFalse(payload["physics_closed"])
        self.assertIn(
            "receiver-sector effective cross equation of state",
            " ".join(payload["assumptions"]),
        )

    def test_positive_branch_contains_pressure_terms(self) -> None:
        branch = build_payload()["positive_branch"]

        self.assertIn("H_minus(1+w_minus)", branch["transport_condition"])
        self.assertIn("H_plus(1+w_cross_plus)", branch["transport_condition"])
        self.assertIn("a_minus^(3(1+w_minus))", branch["constant_w_integral"])
        self.assertIn("3(1+w_minus)-n_det_plus", branch["power_law_b_case"])
        self.assertIn("w_minus=w_cross_plus=0", branch["dust_limit"])

    def test_negative_branch_is_symmetric(self) -> None:
        branch = build_payload()["negative_branch"]

        self.assertIn("H_plus(1+w_plus)", branch["transport_condition"])
        self.assertIn("H_minus(1+w_cross_minus)", branch["transport_condition"])
        self.assertIn("a_plus^(3(1+w_plus))", branch["constant_w_integral"])
        self.assertIn("3(1+w_plus)-n_det_minus", branch["power_law_b_case"])
        self.assertIn("w_plus=w_cross_minus=0", branch["dust_limit"])

    def test_blockers_keep_tensor_closure_open(self) -> None:
        blockers = " ".join(build_payload()["blockers"])

        self.assertIn("anisotropic stress", blockers)
        self.assertIn("Q_cross optical projection remains separate", blockers)
        self.assertIn("K_plus/K_minus tensor maps", blockers)

    def test_notation_names_metric_and_fluid_layers_separately(self) -> None:
        notation = build_payload()["notation"]

        self.assertIn("det4_metric_plus", notation)
        self.assertIn("transport_pf_plus", notation)
        self.assertIn("weight_pf_plus", notation)

    def test_positive_transport_condition_closes_receiver_continuity(self) -> None:
        h_plus, h_minus, w_minus, w_cross, dln_det = sp.symbols(
            "H_plus H_minus w_minus w_cross dln_det"
        )
        dln_rho_minus = -3 * h_minus * (1 + w_minus)
        dln_transport = (
            3 * h_minus * (1 + w_minus)
            - 3 * h_plus * (1 + w_cross)
            - dln_det
        )
        dln_x = dln_det + dln_transport + dln_rho_minus
        residual = sp.simplify(dln_x + 3 * h_plus * (1 + w_cross))

        self.assertEqual(residual, 0)

    def test_negative_transport_condition_closes_receiver_continuity(self) -> None:
        h_plus, h_minus, w_plus, w_cross, dln_det = sp.symbols(
            "H_plus H_minus w_plus w_cross dln_det"
        )
        dln_rho_plus = -3 * h_plus * (1 + w_plus)
        dln_transport = (
            3 * h_plus * (1 + w_plus)
            - 3 * h_minus * (1 + w_cross)
            - dln_det
        )
        dln_x = dln_det + dln_transport + dln_rho_plus
        residual = sp.simplify(dln_x + 3 * h_minus * (1 + w_cross))

        self.assertEqual(residual, 0)


if __name__ == "__main__":
    unittest.main()
