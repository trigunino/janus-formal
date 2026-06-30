from __future__ import annotations

import unittest

from scripts.build_p0_fermi_walker_transport_branch import build_payload


class P0FermiWalkerTransportBranchTests(unittest.TestCase):
    def test_branch_is_lorentz_candidate_not_physics_closure(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["lorentz_preserving"])
        self.assertTrue(payload["minimal_rotation_written"])
        self.assertTrue(payload["dust_force_closed_conditionally"])
        self.assertFalse(payload["source_derived"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_definition_sets_rest_space_rotation_to_zero(self) -> None:
        definition = " ".join(build_payload()["branch_definition"])

        self.assertIn("Omega_alpha=(D_alpha L)L^{-1}", definition)
        self.assertIn("Omega_{alpha AB}=-Omega_{alpha BA}", definition)
        self.assertIn("P Omega_u P = 0", definition)

    def test_plus_and_minus_receiver_geodesic_targets_are_present(self) -> None:
        payload = build_payload()

        self.assertIn("D_plus", payload["plus_branch"]["receiver_force_target"])
        self.assertIn("D_minus", payload["minus_branch"]["receiver_force_target"])
        self.assertIn("Omega_{u,-to+}^{AB}=0", payload["plus_branch"]["fermi_walker_result"])
        self.assertIn("Omega_{u,+to-}^{AB}=0", payload["minus_branch"]["fermi_walker_result"])

    def test_qcross_is_not_used_as_hidden_amplitude(self) -> None:
        qcross = " ".join(build_payload()["qcross_effect"])

        self.assertIn("preserves the local boost-derived Q_cross", qcross)
        self.assertIn("cannot be used as hidden lensing amplitudes", qcross)

    def test_open_items_keep_branch_non_predictive(self) -> None:
        payload = build_payload()
        open_items = " ".join(payload["what_it_does_not_fix"])
        acceptance = " ".join(payload["acceptance_tests"])

        self.assertIn("does not derive the transported receiver-geodesic equation", open_items)
        self.assertIn("does not fix B_plus/B_minus", open_items)
        self.assertIn("does not transport pressure or anisotropic stress", open_items)
        self.assertIn("R_plus=0 and R_minus=0", acceptance)


if __name__ == "__main__":
    unittest.main()
