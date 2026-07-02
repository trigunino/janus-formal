import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_master_acoustic_calculator_component_spectra_gate import build_payload as component_payload
from scripts.build_p0_eft_janus_z4_master_acoustic_calculator_shape_phase_damping_gate import build_payload as shape_payload
from scripts.build_p0_eft_janus_z4_master_solver_provenance_manifest_gate import build_payload as provenance_payload
from scripts.build_p0_eft_janus_z4_master_solver_implementation_readiness_gate import build_payload as readiness_payload


class P0EFTJanusZ4MasterSolverImplementationChainTests(unittest.TestCase):
    def test_solver_chain_reaches_internal_diagnostic_readiness_only(self):
        component = component_payload()
        shape = shape_payload()
        provenance = provenance_payload()
        readiness = readiness_payload()

        self.assertTrue(component["internal_diagnostic_spectra_generated"])
        self.assertTrue(shape["internal_shape_phase_damping_diagnostics_ready"])
        self.assertTrue(Path(provenance["manifest_path"]).exists())
        self.assertTrue(readiness["solver_implemented"])
        self.assertEqual(readiness["solver_scope"], "internal_diagnostic_cmb_generation_only")
        self.assertFalse(readiness["observed_planck_validation"])
        self.assertFalse(readiness["observed_likelihood_allowed"])
        self.assertFalse(readiness["candidate_promotion_allowed"])
        self.assertFalse(readiness["retuning_allowed"])
        self.assertFalse(readiness["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
