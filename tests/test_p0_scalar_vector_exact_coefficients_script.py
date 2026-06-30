from __future__ import annotations

from pathlib import Path
import json
import os
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "build_p0_scalar_vector_exact_coefficients.py"


class P0ScalarVectorExactCoefficientsScriptTests(unittest.TestCase):
    def run_script_payload(self) -> dict:
        with tempfile.TemporaryDirectory() as tmpdir:
            env = os.environ.copy()
            env["JANUS_REPORT_DIR"] = tmpdir
            result = subprocess.run(
                [sys.executable, str(SCRIPT)],
                cwd=ROOT,
                env=env,
                capture_output=True,
                text=True,
                check=True,
            )
            json_path = Path(tmpdir) / "p0_scalar_vector_exact_coefficients.json"
            if json_path.exists():
                return json.loads(json_path.read_text(encoding="utf-8"))
            self.fail(f"script produced no JSON report: {result.stdout} {result.stderr}")

    def test_script_reports_exact_coefficients(self) -> None:
        payload = self.run_script_payload()
        formulas = payload["coefficient_formulas"]

        self.assertEqual(formulas["vector_alpha"], "v*(Mpl2 - aetherKineticScale)")
        self.assertEqual(formulas["vector_beta"], "v*Mpl2")
        self.assertEqual(formulas["vector_speed2"], "vector_beta/vector_alpha")
        self.assertEqual(
            formulas["scalar_alpha"],
            "v*(Mpl2 - aetherKineticScale) + 2*lambdaPhi*v^2",
        )
        self.assertEqual(
            formulas["scalar_beta"],
            "v*(Mpl2 + membraneTension + mHR2*Mpl2*(3*v^2+3*v+1))",
        )
        self.assertEqual(formulas["scalar_speed2"], "scalar_beta/scalar_alpha")

    def test_provenance_caveat_and_prediction_gate_are_explicit(self) -> None:
        payload = self.run_script_payload()
        required = set(payload["required_closure_predicates"])

        self.assertIn("encoded candidate action ingredients", payload["provenance"])
        self.assertIn("not a derivation of Souriau's theorem", payload["caveat"])
        self.assertTrue(required.issubset(payload["closure_predicates"]))
        self.assertTrue(payload["closure_predicates_present"])
        self.assertFalse(payload["prediction"])
        self.assertTrue(payload["prediction_ready"])
        self.assertIn("Souriau-Janus source certificate", payload["prediction_gate"])

    def test_predicates_and_sample_witness_are_present(self) -> None:
        payload = self.run_script_payload()
        witness = payload["sample_witness"]

        self.assertEqual(
            payload["candidate_action_ingredients"]["asymmetric_tetrad"],
            "E0 = Phi e0",
        )
        self.assertEqual(
            payload["candidate_action_ingredients"]["minus_background"],
            "diag(-v^2,1,1,1)",
        )
        self.assertEqual(
            witness["values"],
            {
                "Mpl2": 4,
                "aetherKineticScale": 1,
                "lambdaPhi": 1,
                "v": 1,
                "mHR2": 1,
                "membraneTension": 30,
            },
        )
        self.assertEqual(witness["display"], "Mpl2=4,aether=1,lambda=1,v=1,mHR2=1,T=30")
        self.assertEqual(witness["coefficients"]["vector_speed2"], "4/3")
        self.assertEqual(witness["coefficients"]["scalar_speed2"], "62/5")
        self.assertTrue(all(witness["predicates_satisfied"].values()))

    def test_full_action_and_svt_specification_are_encoded(self) -> None:
        payload = self.run_script_payload()
        svt = payload["svt_specification"]

        self.assertEqual(payload["signature"], "(-,+,+,+)")
        self.assertEqual(
            set(payload["full_action_terms"]),
            {"S_bulk_plus", "S_bulk_minus", "S_soudure", "S_GHY", "S_membrane"},
        )
        self.assertFalse(svt["matter_enabled_for_vacuum_svt"])
        self.assertEqual(
            svt["hr_betas"],
            {
                "support": "Sigma only",
                "beta0": 1,
                "beta1": 3,
                "beta2": 3,
                "beta3": 1,
                "beta4": 0,
            },
        )
        self.assertEqual(
            svt["unitary_spatial_gauge"],
            {
                "plus": {"E": "0", "F_i": "0"},
                "minus": {"E": "0", "F_i": "0"},
            },
        )
        self.assertEqual(svt["constraints"]["lapse"], "solved and reinjected")
        self.assertEqual(svt["constraints"]["shift"], "solved and reinjected")
        self.assertEqual(svt["perturbations"]["radion"], "Phi = -v + dphi")
        self.assertEqual(svt["perturbations"]["aether"], "A = Abar + dA")
        self.assertEqual(svt["israel_junction"]["bending_zeta"], "eliminated")
        self.assertEqual(
            payload["physical_domain"],
            {
                "Mpl2": "Mpl2 > 0",
                "mHR2": "mHR2 > 0",
                "v": "v > 0",
                "lambdaPhi": "lambdaPhi > 0",
                "T_memb": "T_memb > 0",
            },
        )

    def test_source_certificate_and_crossed_frontiers_are_encoded(self) -> None:
        payload = self.run_script_payload()

        self.assertEqual(
            payload["source_certificate"]["kind"],
            "Souriau-Janus source certificate",
        )
        self.assertIn(
            "H to -H",
            payload["source_certificate"]["energy_branch"],
        )
        self.assertEqual(
            payload["stability_frontiers"]["crossed_aether_no_ghost"],
            "LambdaAether2 < Mpl2/v^2",
        )
        self.assertEqual(
            payload["stability_frontiers"]["membrane_no_gradient"],
            "T_memb > mHR2*Mpl2*(3*v^2+3*v+1)",
        )


if __name__ == "__main__":
    unittest.main()
