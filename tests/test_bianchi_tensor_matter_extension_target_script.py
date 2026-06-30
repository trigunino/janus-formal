from __future__ import annotations

import unittest

from scripts.build_bianchi_tensor_matter_extension_target import build_payload


class BianchiTensorMatterExtensionTargetTests(unittest.TestCase):
    def test_prediction_is_not_ready_and_dust_is_not_enough(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["prediction_ready"])
        self.assertFalse(payload["dust_assumptions_enough"])
        self.assertFalse(payload["perfect_fluid_target"]["closed"])
        self.assertFalse(payload["anisotropic_stress_target"]["closed"])

    def test_pressure_projector_pi_and_divergence_terms_are_tracked(self) -> None:
        terms = {term["term"] for term in build_payload()["tensor_terms_needing_transport"]}

        self.assertIn("pressure_metric_term", terms)
        self.assertIn("projector", terms)
        self.assertIn("anisotropic_stress", terms)
        self.assertIn("equation_of_state", terms)
        self.assertIn("divergence_terms", terms)

    def test_scalar_qcross_qdet_absorption_is_forbidden(self) -> None:
        forbidden = " ".join(build_payload()["forbidden_shortcuts"])

        self.assertIn("do not absorb pressure into scalar Q_cross", forbidden)
        self.assertIn("do not absorb pressure into scalar Q_det", forbidden)
        self.assertIn("do not absorb Pi^{mu nu} into scalar Q_cross", forbidden)
        self.assertIn("do not absorb Pi^{mu nu} into scalar Q_det", forbidden)

    def test_tensor_extension_requires_same_transport_maps(self) -> None:
        required = " ".join(build_payload()["required_before_closure"])

        self.assertIn("same L_minus_to_plus/L_plus_to_minus maps", required)
        self.assertIn("K_plus/K_minus", required)
        self.assertIn("optical Q_cross", required)


if __name__ == "__main__":
    unittest.main()
