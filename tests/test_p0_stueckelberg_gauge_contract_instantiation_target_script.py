from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_gauge_contract_instantiation_target import build_payload


class P0GaugeContractInstantiationTargetTests(unittest.TestCase):
    def test_instantiation_target_defined_but_not_data_ready(self) -> None:
        payload = build_payload()
        decision = payload["decision"]

        self.assertTrue(decision["instantiation_target_defined"])
        self.assertTrue(decision["contract_fields_complete"])
        self.assertFalse(decision["instantiated_with_data"])
        self.assertFalse(payload["prediction_ready"])

    def test_fields_include_tetrad_wavevector_and_branch(self) -> None:
        payload = build_payload()
        names = {row["name"] for row in payload["fields"]}

        self.assertIn("observer_tetrad_id", names)
        self.assertIn("photon_wavevector", names)
        self.assertIn("phi_l_branch_id", names)

    def test_validations_prevent_redshift_and_affine_fits(self) -> None:
        payload = build_payload()
        validations = " ".join(payload["validations"])

        self.assertIn("not fitted", validations)
        self.assertIn("affine normalization", validations)
        self.assertIn("k.k=0", validations)


if __name__ == "__main__":
    unittest.main()
