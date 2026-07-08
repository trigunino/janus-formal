import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_alpha_superselection_observation_endpoint_gate import (
    build_payload,
)


class JanusAlphaSuperselectionObservationEndpointTests(unittest.TestCase):
    def test_sn_without_bao_is_shape_only(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            bao = base / "empty_bao"
            bao.mkdir()
            (base / "jla_likelihood_v6.tgz").write_text("stub", encoding="utf-8")
            payload = build_payload(base, bao)

        self.assertTrue(payload["datasets"]["SN"]["available"])
        self.assertFalse(payload["datasets"]["BAO"]["available"])
        self.assertFalse(payload["full_sector_selection_ready"])
        self.assertEqual(payload["classification"], "ready_for_SN_shape_only")

    def test_sn_plus_bao_is_full_endpoint_ready(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            bao = base / "empty_bao"
            bao.mkdir()
            (base / "jla_likelihood_v6.tgz").write_text("stub", encoding="utf-8")
            (base / "DESI_DR2_BAO.csv").write_text("stub", encoding="utf-8")
            payload = build_payload(base, bao)

        self.assertTrue(payload["full_sector_selection_ready"])
        self.assertEqual(payload["classification"], "ready_for_SN_plus_BAO_sector_selection")


if __name__ == "__main__":
    unittest.main()
