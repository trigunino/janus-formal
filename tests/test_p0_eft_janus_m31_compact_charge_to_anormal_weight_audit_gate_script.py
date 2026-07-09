import unittest

from src.janus_lab.janus_phase_space_occupation_search import (
    m31_compact_charge_to_anormal_weight_audit_payload,
)


class JanusM31CompactChargeToANormalWeightAuditGateTests(unittest.TestCase):
    def test_published_charge_sector_is_relevant_but_not_closed(self):
        payload = m31_compact_charge_to_anormal_weight_audit_payload()
        self.assertTrue(payload["what_it_closes"]["compact_charge_dimensions_declared"])
        self.assertFalse(payload["what_it_does_not_close"]["normal_redshift_generator_A_normal"])
        self.assertFalse(payload["no_fit_closed_now"])

    def test_extension_path_requires_representation_and_four_dissociation(self):
        payload = m31_compact_charge_to_anormal_weight_audit_payload()
        path = " ".join(payload["non_rustine_extension_path"])
        self.assertIn("representation on the C11 mode bundle", path)
        self.assertIn("four-dissociated", path)


if __name__ == "__main__":
    unittest.main()
