import unittest

from scripts.build_p0_eft_janus_z2_global_state_formal_asset_inventory import build_payload


class GlobalStateFormalAssetInventoryTests(unittest.TestCase):
    def test_existing_formal_assets_are_indexed(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertIn("projected_baryon_noether_charge", payload["assets"])
        self.assertIn("souriau_boundary_hamiltonian", payload["assets"])
        self.assertIn("global_bimetric_state_to_sector_normalization", payload["assets"])

    def test_assets_do_not_close_absolute_normalization(self):
        payload = build_payload()

        self.assertTrue(
            all(not asset["closes_absolute_normalization"] for asset in payload["assets"].values())
        )
        self.assertIn("global_bimetric_stress_energy_state_inputs.json", payload["next_required"][0])


if __name__ == "__main__":
    unittest.main()
