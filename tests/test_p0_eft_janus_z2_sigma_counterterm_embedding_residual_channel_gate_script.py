import unittest

from scripts.build_p0_eft_janus_z2_sigma_counterterm_embedding_residual_channel_gate import build_payload


class P0EFTJanusZ2SigmaCountertermEmbeddingResidualChannelGateTests(unittest.TestCase):
    def test_embedding_channel_ledger_is_declared_without_fit(self):
        payload = build_payload()

        self.assertTrue(payload["counterterm_embedding_residual_channel_ledger_declared"])
        self.assertTrue(payload["declared"]["delta_X_variation_basis_declared"])
        self.assertIn("fit embedding residual coefficient", payload["forbidden"])

    def test_embedding_channel_remains_open_until_coefficient_is_explicit(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["embedding_residual_coefficient_explicit"])
        self.assertFalse(payload["counterterm_embedding_residual_channel_ready"])
        self.assertIn("derive_active_X_pm_of_a", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
