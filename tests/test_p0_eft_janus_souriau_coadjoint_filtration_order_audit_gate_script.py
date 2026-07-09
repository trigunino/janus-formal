import unittest

from src.janus_lab.janus_phase_space_occupation_search import (
    souriau_coadjoint_filtration_order_audit_payload,
)


class JanusSouriauCoadjointFiltrationOrderAuditGateTests(unittest.TestCase):
    def test_filtration_is_real_but_too_coarse(self):
        payload = souriau_coadjoint_filtration_order_audit_payload()
        self.assertTrue(payload["coadjoint_filtration_derived"])
        self.assertEqual(payload["filtration_dimension"], 11)
        self.assertEqual(payload["block_profile_levels_on_Sym4"], 15)
        self.assertFalse(payload["orders_1001_states"])

    def test_full_component_order_remains_missing(self):
        payload = souriau_coadjoint_filtration_order_audit_payload()
        self.assertFalse(payload["full_component_order_derived"])
        self.assertFalse(payload["no_fit_closed_now"])


if __name__ == "__main__":
    unittest.main()
