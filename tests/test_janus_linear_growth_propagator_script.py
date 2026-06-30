from __future__ import annotations

from argparse import Namespace
import unittest

from janus_lab.models import JanusExpansion
from scripts.build_janus_linear_growth_propagator import build_payload, integrate_mode


class JanusLinearGrowthPropagatorTests(unittest.TestCase):
    def test_propagator_is_diagnostic_not_amplitude_normalized(self) -> None:
        payload = build_payload(
            Namespace(
                q0=-0.087,
                a_initial=0.2,
                a_final=1.0,
                samples=16,
                omega_plus=0.5,
                omega_minus=0.5,
            )
        )

        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["amplitude_normalized"])
        self.assertEqual(
            payload["omega_inputs"]["status"],
            "declared diagnostic inputs, not fitted observables",
        )

    def test_source_mode_grows_more_than_null_mode(self) -> None:
        payload = build_payload(
            Namespace(
                q0=-0.087,
                a_initial=0.2,
                a_final=1.0,
                samples=16,
                omega_plus=0.5,
                omega_minus=0.5,
            )
        )

        self.assertGreater(
            payload["modes"]["source"]["final_value"],
            payload["modes"]["null"]["final_value"],
        )
        self.assertGreater(payload["eigenvalues"]["source"], 0.0)

    def test_null_mode_with_zero_derivative_stays_constant(self) -> None:
        mode = integrate_mode(
            JanusExpansion.from_q0(-0.087),
            a_initial=0.2,
            a_final=1.0,
            samples=16,
            eigenvalue=0.0,
        )

        self.assertAlmostEqual(mode["final_value"], 1.0)
        self.assertAlmostEqual(mode["final_d_dln_a"], 0.0)

    def test_invalid_inputs_raise(self) -> None:
        model = JanusExpansion.from_q0(-0.087)

        with self.assertRaisesRegex(ValueError, "samples"):
            integrate_mode(model, a_initial=0.2, a_final=1.0, samples=1, eigenvalue=0.0)

        with self.assertRaisesRegex(ValueError, "z_max"):
            integrate_mode(model, a_initial=0.01, a_final=1.0, samples=4, eigenvalue=0.0)

        with self.assertRaisesRegex(ValueError, "non-negative"):
            build_payload(
                Namespace(
                    q0=-0.087,
                    a_initial=0.2,
                    a_final=1.0,
                    samples=16,
                    omega_plus=-0.1,
                    omega_minus=0.5,
                )
            )


if __name__ == "__main__":
    unittest.main()
