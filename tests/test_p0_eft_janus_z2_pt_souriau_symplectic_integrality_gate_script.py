import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_pt_souriau_symplectic_integrality_gate import (
    build_payload,
)


class PTSouriauSymplecticIntegralityGateTests(unittest.TestCase):
    def test_live_integrality_is_blocked(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["symplectic_integrality_ready"])
        self.assertIn("periods_over_two_cycles_computed", payload["blocked_by"])

    def test_integrality_can_write_frontier_inputs_when_complete(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            inp = root / "inputs.json"
            out = root / "frontier.json"
            inp.write_text(
                json.dumps(
                    {
                        "boundary_phase_space_declared": True,
                        "symplectic_two_form_Omega_PT_declared": True,
                        "Omega_PT_closed": True,
                        "prequantum_integrality_condition_declared": True,
                        "periods_over_two_cycles_computed": True,
                        "periods_are_integer_multiples_of_2pi_hbar": True,
                        "mass_moment_map_period_identified": True,
                        "minimal_positive_period_nonzero": True,
                        "PT_sign_pairing_preserves_lattice": True,
                        "unit_value_kg_derived": False,
                    }
                ),
                encoding="utf-8",
            )

            payload = build_payload(input_path=inp, output_path=out, write_output=True)
            written = json.loads(out.read_text(encoding="utf-8"))

        self.assertTrue(payload["symplectic_integrality_ready"])
        self.assertTrue(written["charge_lattice_integrality_derived"])
        self.assertTrue(written["minimal_mass_unit_derived"])


if __name__ == "__main__":
    unittest.main()
