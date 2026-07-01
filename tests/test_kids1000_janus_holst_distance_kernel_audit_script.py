from __future__ import annotations

import unittest

from scripts.build_kids1000_janus_holst_distance_kernel_audit import build_payload, distance_kernel_options


class KiDS1000JanusHolstDistanceKernelAuditTests(unittest.TestCase):
    def test_distance_kernel_options_include_current_and_angular(self) -> None:
        self.assertEqual(
            distance_kernel_options(),
            [
                "comoving",
                "comoving_standard_jacobi",
                "angular_lens",
                "angular_lens_standard_jacobi",
            ],
        )

    def test_payload_is_diagnostic(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["dimension"], 75)
        self.assertEqual(len(payload["rows"]), 4)
        self.assertFalse(payload["prediction_ready"])


if __name__ == "__main__":
    unittest.main()
