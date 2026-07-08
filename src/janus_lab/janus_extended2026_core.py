from __future__ import annotations

from dataclasses import dataclass

from .janus_2024_bulk_path import Janus2024BulkObservablePath, build_cited_bulk_reference_path
from .janus_2024_cited_calibration import (
    Janus2024CitedCalibration,
    published_janus_2024_cited_calibration,
)


@dataclass(frozen=True)
class JanusExtended2026Core:
    """Minimal executable source bundle for the Janus 2024-2026 cosmology core.

    This object is intentionally conservative. It exposes only the source family
    and formula layers that are already verified and already linked to executable
    code in this repo.
    """

    source_ids: tuple[str, ...] = (
        "M30",
        "M18",
        "X2026-expansion-desi",
        "X2026-variable-constants",
        "X2025-technical-book",
    )
    verified_equation_anchors: tuple[str, ...] = (
        "M18 Eq. 10 exact expansion a(u), t(u)",
        "M18 Eq. 13 deceleration q(u)",
        "M18 Eq. 14 curvature/H conversion",
        "M18 Eqs. 15-17 open marker distance",
        "X2026-expansion-desi Eqs. 27-29 exact-solution/energy condition",
        "X2026-variable-constants Eq. 40 final gauge set",
    )
    verified_source_claims: tuple[str, ...] = (
        "X2026-expansion-desi claims stronger past acceleration consistent with DESI-era hints",
        "X2026-variable-constants proposes a variable-constants early-universe regime",
    )

    def cited_calibration(self) -> Janus2024CitedCalibration:
        return published_janus_2024_cited_calibration()

    def bulk_reference_path(self, *, z_max: float = 5.0, samples: int = 512) -> Janus2024BulkObservablePath:
        calibration = self.cited_calibration()
        return build_cited_bulk_reference_path(
            reference=calibration.to_reference(),
            q0=calibration.q0,
            h0_s_inv=calibration.h0_s_inv,
            alpha_seconds=calibration.alpha_seconds,
            z_max=z_max,
            samples=samples,
        )

    @staticmethod
    def variable_constants_eq40_exponents() -> dict[str, float]:
        return {
            "c_hat": -0.5,
            "h_hat": 1.5,
            "g_hat": -1.0,
            "e_hat": 0.5,
            "m_hat": 1.0,
            "t_hat": 1.5,
            "mu0_hat": 1.0,
            "characteristic_length": 1.0,
        }

    @staticmethod
    def current_blockers() -> tuple[str, ...]:
        return (
            "native_bao_ruler_derivation_missing",
            "absolute_background_normalization_not_paper-native",
            "full_cmb_observable_path_missing",
            "2026_source_claims_not_independently_validated",
        )


def published_janus_extended2026_core() -> JanusExtended2026Core:
    return JanusExtended2026Core()
