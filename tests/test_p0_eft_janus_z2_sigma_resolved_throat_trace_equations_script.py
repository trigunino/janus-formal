import unittest

from scripts.derive_p0_eft_janus_z2_sigma_resolved_throat_trace_equations import (
    build_payload,
)


class ResolvedThroatTraceEquationsTests(unittest.TestCase):
    def test_trace_equations_derive_obstruction_without_closure_claim(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["R_h_trace_equation_derived"])
        self.assertTrue(payload["R_K_trace_equation_derived"])
        self.assertFalse(payload["R_h_trace_value_ready"])
        self.assertFalse(payload["R_K_trace_value_ready"])
        self.assertFalse(payload["minimal_constant_basis_closes"])
        self.assertIn("surface_stress_trace_target", payload["equations"]["israel_trace"])
        self.assertIn("do_not_set_c3_by_fit", payload["forbidden_shortcuts"])


if __name__ == "__main__":
    unittest.main()
