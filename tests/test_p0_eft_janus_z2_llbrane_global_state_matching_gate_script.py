import json
import math
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_llbrane_global_state_matching_gate import (
    build_payload,
    chi_from_mass,
    mass_from_chi,
)


class LLBraneGlobalStateMatchingGateTests(unittest.TestCase):
    def test_missing_inputs_do_not_select_scale(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            payload = build_payload(
                chi_path=base / "chi.json",
                mass_path=base / "mass.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["absolute_scale_selected"])
        self.assertFalse(payload["reduces_two_parameters_to_one"])

    def test_single_chi_input_infers_mass_but_keeps_one_parameter(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            chi_path = base / "chi.json"
            chi_path.write_text(json.dumps({"chi_LL_abs_inverse_m": 2.0}), encoding="utf-8")
            payload = build_payload(chi_path=chi_path, mass_path=base / "missing.json")

        self.assertFalse(payload["gate_passed"])
        self.assertTrue(payload["reduces_two_parameters_to_one"])
        self.assertAlmostEqual(payload["inferred"]["M_from_chi_kg"], mass_from_chi(2.0))

    def test_matching_inputs_pass_consistency(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            mass = 3.0
            chi = chi_from_mass(mass)
            chi_path = base / "chi.json"
            mass_path = base / "mass.json"
            chi_path.write_text(json.dumps({"chi_LL_abs_inverse_m": chi}), encoding="utf-8")
            mass_path.write_text(json.dumps({"M_bridge_kg": mass}), encoding="utf-8")
            payload = build_payload(chi_path=chi_path, mass_path=mass_path)

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["matching_passed"])
        self.assertTrue(math.isclose(payload["inferred"]["M_from_chi_kg"], mass))
        self.assertFalse(payload["absolute_scale_selected"])


if __name__ == "__main__":
    unittest.main()
