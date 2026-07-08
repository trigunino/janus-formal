import unittest

from scripts.build_p0_eft_janus_radical_quantum_geometry_reconstruction_gate import (
    build_payload,
)


class JanusRadicalQuantumGeometryReconstructionTests(unittest.TestCase):
    def test_distinguishes_from_previous_quantum_first(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["distinction_from_previous_quantum_first"]["already_tried"])
        self.assertFalse(payload["alpha_generated_no_fit"])

    def test_all_required_maps_remain_open(self):
        payload = build_payload()

        self.assertEqual(len(payload["required_maps"]), 4)
        self.assertTrue(all(not row["closed"] for row in payload["required_maps"]))


if __name__ == "__main__":
    unittest.main()
