import unittest

from janus_lab.janus_phase_space_occupation_search import (
    m31_coadjoint_rho_transfer_attempt_payload,
)


class JanusM31CoadjointRhoTransferAttemptGateTests(unittest.TestCase):
    def test_rho_candidate_progresses_but_no_normal_hamiltonian(self):
        payload = m31_coadjoint_rho_transfer_attempt_payload()

        self.assertTrue(payload["what_progresses"]["rho_candidate_from_M31_available"])
        self.assertTrue(payload["what_progresses"]["standard_lift_to_Sym4_available"])
        self.assertFalse(payload["normal_redshift_generator_found"])

    def test_all_available_generators_fail_normal_role(self):
        payload = m31_coadjoint_rho_transfer_attempt_payload()

        self.assertEqual(payload["inputs"]["target_dimension"], 1001)
        self.assertTrue(all(row["rho_available"] for row in payload["generator_audit"]))
        self.assertFalse(any(row["normal_redshift_H"] for row in payload["generator_audit"]))


if __name__ == "__main__":
    unittest.main()
