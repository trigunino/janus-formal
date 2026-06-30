from __future__ import annotations

import unittest

from scripts.build_p0_split_noether_calculable_target import build_payload


class P0SplitNoetherCalculableTargetTests(unittest.TestCase):
    def test_target_is_written_but_not_proved_or_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "split-noether-calculable-target-open")
        self.assertTrue(payload["replaces_noether_like_constraints"])
        self.assertTrue(payload["split_noether_identities_written"])
        self.assertFalse(payload["split_noether_identities_proved"])
        self.assertFalse(payload["can_eliminate_phi_family_now"])
        self.assertTrue(payload["linear_phi_candidate_available"])
        self.assertTrue(payload["linear_imatter_tensor_contract_available"])
        self.assertTrue(payload["linear_imatter_metric_variation_available"])
        self.assertTrue(payload["linear_imatter_stress_response_target_available"])
        self.assertTrue(payload["linear_imatter_l_variation_available"])
        self.assertTrue(payload["linear_imatter_lorentz_projected_el_available"])
        self.assertFalse(payload["prediction_ready"])

    def test_objects_cover_metric_and_map_variations(self) -> None:
        objects = {row["object"]: row["definition"] for row in build_payload()["objects"]}

        self.assertIn("K_plus", objects)
        self.assertIn("K_minus", objects)
        self.assertIn("E_phi", objects)
        self.assertIn("E_L", objects)
        self.assertIn("delta S_couple/delta g_plus", objects["K_plus"])
        self.assertIn("delta S_couple/delta L", objects["E_L"])

    def test_identities_cover_rplus_rminus_and_on_shell_map_equations(self) -> None:
        identities = " ".join(row["identity"] + row["closed_on_shell_if"] for row in build_payload()["identities"])

        self.assertIn("R_plus", identities)
        self.assertIn("R_minus", identities)
        self.assertIn("E_phi=0", identities)
        self.assertIn("E_L=0", identities)
        self.assertIn("minus diffeo", identities)


if __name__ == "__main__":
    unittest.main()
