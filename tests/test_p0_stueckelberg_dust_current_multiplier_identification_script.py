from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_dust_current_multiplier_identification import build_payload


class P0DustCurrentMultiplierIdentificationTests(unittest.TestCase):
    def test_dust_current_identification_is_rejected(self) -> None:
        payload = build_payload()
        decision = payload["decision"]

        self.assertFalse(decision["dust_current_identification_works"])
        self.assertTrue(decision["orthogonality_obstruction_found"])
        self.assertFalse(decision["accepted_as_final_closure"])
        self.assertFalse(payload["prediction_ready"])

    def test_parallel_current_cannot_enforce_transverse_acceleration(self) -> None:
        payload = build_payload()
        text = " ".join(payload["needed_projection"])

        self.assertIn("transverse projector", text)
        self.assertIn("no preferred transverse vector", text)
        self.assertTrue(payload["decision"]["transverse_multiplier_needed"])

    def test_both_mirror_identifications_fail(self) -> None:
        payload = build_payload()

        self.assertEqual(len(payload["identifications"]), 2)
        self.assertTrue(all(not row["works_as_vector_multiplier"] for row in payload["identifications"]))


if __name__ == "__main__":
    unittest.main()
