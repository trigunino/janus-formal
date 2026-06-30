from __future__ import annotations

import unittest

import sympy as sp

from scripts.build_p0_janus_weakfield_lorentz_projection_derivation import (
    ETA,
    build_payload,
    eta_skew_projection,
    eta_symmetric_part,
    render_markdown,
    scalar_weakfield_a_matrix,
)


class P0JanusWeakfieldLorentzProjectionDerivationTests(unittest.TestCase):
    def test_eta_skew_projection_satisfies_lorentz_algebra(self) -> None:
        symbols = sp.symbols("a00:04 a10:14 a20:24 a30:34")
        matrix = sp.Matrix(4, 4, symbols)
        projected = eta_skew_projection(matrix)

        self.assertEqual(sp.simplify(projected.T * ETA + ETA * projected), sp.zeros(4))

    def test_scalar_weakfield_projection_is_zero(self) -> None:
        projected = eta_skew_projection(scalar_weakfield_a_matrix())

        self.assertEqual(projected, sp.zeros(4))

    def test_scalar_weakfield_is_symmetric_stretch(self) -> None:
        matrix = scalar_weakfield_a_matrix()

        self.assertEqual(eta_symmetric_part(matrix), matrix)

    def test_payload_selects_only_comoving_scalar_identity_branch(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "weakfield-lorentz-projection-derived-open")
        self.assertTrue(payload["lorentz_projection_formula_derived"])
        self.assertTrue(payload["scalar_weakfield_lorentz_generator_zero"])
        self.assertTrue(payload["symmetric_stretch_rejected_as_qcross"])
        self.assertTrue(payload["comoving_scalar_same_l_identity_conditionally_selected"])
        self.assertTrue(payload["noncomoving_boost_source_required"])
        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_markdown_keeps_noncomoving_branch_open(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Non-comoving boost source required: True", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
