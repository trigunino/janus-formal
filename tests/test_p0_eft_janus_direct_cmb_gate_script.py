from __future__ import annotations

import unittest

from scripts.build_p0_eft_janus_direct_cmb_gate import build_payload


class P0EFTJanusDirectCMBGateTests(unittest.TestCase):
    def test_gate_refuses_lcdm_compressed_verdict(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-direct-cmb-observable-gate-open")
        self.assertFalse(payload["uses_lcdm_compressed_planck_parameters_as_verdict"])
        self.assertFalse(payload["direct_cmb_likelihood_ready"])
        self.assertFalse(payload["janus_holst_distance_ruler_map_ready"])

    def test_distance_and_ruler_are_blockers(self) -> None:
        payload = build_payload()
        blockers = " ".join(payload["blocking_inputs"])

        self.assertIn("angular diameter distance", blockers)
        self.assertIn("sound horizon", blockers)


if __name__ == "__main__":
    unittest.main()
