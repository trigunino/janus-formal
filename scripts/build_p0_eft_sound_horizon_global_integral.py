from __future__ import annotations

from pathlib import Path
from functools import lru_cache
import json
import math

try:
    from scripts.build_p0_eft_holst_plasma_delta_neff_derivation import build_payload as delta_neff_payload
    from scripts.build_p0_eft_sound_horizon_drag_target import build_payload as sound_target_payload
except ModuleNotFoundError:
    from build_p0_eft_holst_plasma_delta_neff_derivation import build_payload as delta_neff_payload
    from build_p0_eft_sound_horizon_drag_target import build_payload as sound_target_payload


REPORT_PATH = Path("outputs/reports/p0_eft_sound_horizon_global_integral.md")
JSON_PATH = Path("outputs/reports/p0_eft_sound_horizon_global_integral.json")

OMEGA_GAMMA_H2 = 2.469e-5
NEUTRINO_FACTOR = 0.22710731766
TCMB_SCALE = 2.7255 / 2.7


def z_drag_eisenstein_hu(omega_b_h2: float, omega_m_h2: float) -> float:
    b1 = 0.313 * omega_m_h2**-0.419 * (1.0 + 0.607 * omega_m_h2**0.674)
    b2 = 0.238 * omega_m_h2**0.223
    return (
        1291.0
        * omega_m_h2**0.251
        / (1.0 + 0.659 * omega_m_h2**0.828)
        * (1.0 + b1 * omega_b_h2**b2)
    )


def sound_speed(z: float, omega_b_h2: float) -> float:
    r_b = 31500.0 * omega_b_h2 * TCMB_SCALE**-4 / (1.0 + z)
    return 1.0 / math.sqrt(3.0 * (1.0 + r_b))


def h_physical(z: float, omega_m_h2: float, neff: float) -> float:
    omega_r_h2 = OMEGA_GAMMA_H2 * (1.0 + NEUTRINO_FACTOR * neff)
    zp1 = 1.0 + z
    return math.sqrt(omega_m_h2 * zp1**3 + omega_r_h2 * zp1**4)


def sound_horizon_unit(
    omega_b_h2: float,
    omega_m_h2: float,
    neff: float,
    z_drag: float,
    z_max: float = 1.0e7,
    samples: int = 5000,
) -> float:
    y0 = math.log1p(z_drag)
    y1 = math.log1p(z_max)
    dy = (y1 - y0) / (samples - 1)
    total = 0.0
    prev = None
    for i in range(samples):
        y = y0 + i * dy
        z = math.exp(y) - 1.0
        value = sound_speed(z, omega_b_h2) * (1.0 + z) / h_physical(z, omega_m_h2, neff)
        if prev is not None:
            total += 0.5 * dy * (prev + value)
        prev = value
    return total


def solve_delta_neff_for_ratio(
    target_ratio: float,
    omega_b_h2: float,
    omega_m_h2: float,
    neff_ref: float,
    z_drag: float,
) -> float:
    rd_ref = sound_horizon_unit(omega_b_h2, omega_m_h2, neff_ref, z_drag)
    lo = 0.0
    hi = 10.0
    for _ in range(80):
        mid = 0.5 * (lo + hi)
        ratio = sound_horizon_unit(omega_b_h2, omega_m_h2, neff_ref + mid, z_drag) / rd_ref
        if ratio > target_ratio:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


@lru_cache(maxsize=1)
def build_payload() -> dict:
    target = sound_target_payload()
    delta = delta_neff_payload()
    delta_neff = float(delta["best_candidate"]["value"])
    neff_ref = 3.046
    neff_janus = neff_ref + delta_neff
    omega_b_h2 = 0.02237
    omega_m_h2 = 0.02237 + 0.136
    z_drag = z_drag_eisenstein_hu(omega_b_h2, omega_m_h2)
    rd_ref = sound_horizon_unit(omega_b_h2, omega_m_h2, neff_ref, z_drag)
    rd_janus = sound_horizon_unit(omega_b_h2, omega_m_h2, neff_janus, z_drag)
    ratio = rd_janus / rd_ref
    required = float(target["required_rd_ratio"])
    required_delta_neff = solve_delta_neff_for_ratio(required, omega_b_h2, omega_m_h2, neff_ref, z_drag)
    residual = ratio - required
    return {
        "description": "Direct drag-epoch sound-horizon integral with Janus-Holst Delta N_eff.",
        "status": "sound-horizon-global-integral-computed",
        "omega_b_h2": omega_b_h2,
        "omega_m_h2": omega_m_h2,
        "z_drag_eisenstein_hu": z_drag,
        "neff_ref": neff_ref,
        "delta_neff_janus_holst": delta_neff,
        "neff_janus": neff_janus,
        "rd_ref_unit": rd_ref,
        "rd_janus_unit": rd_janus,
        "rd_ratio_janus_over_ref": ratio,
        "required_rd_ratio_from_bao": required,
        "ratio_residual": residual,
        "abs_ratio_residual": abs(residual),
        "matches_bao_required_shrink": abs(residual) < 0.01,
        "required_delta_neff_for_bao_ratio": required_delta_neff,
        "delta_neff_shortfall": required_delta_neff - delta_neff,
        "is_derived_geometry": bool(delta.get("is_derived_geometry", False)),
        "next_required": (
            "Promote Delta N_eff and the drag-epoch background to a CAMB-native early-H(z) branch; "
            "local visibility hooks are insufficient."
        ),
    }


def render_markdown(payload: dict) -> str:
    return "\n".join(
        [
            "# P0 EFT Sound Horizon Global Integral",
            "",
            payload["description"],
            "",
            f"Status: {payload['status']}",
            f"Derived geometry: {payload['is_derived_geometry']}",
            f"Matches BAO required shrink: {payload['matches_bao_required_shrink']}",
            "",
            "## Result",
            "",
            f"- z_drag: {payload['z_drag_eisenstein_hu']:.6g}",
            f"- Delta N_eff: {payload['delta_neff_janus_holst']:.6g}",
            f"- r_d Janus / r_d ref: {payload['rd_ratio_janus_over_ref']:.6g}",
            f"- required ratio: {payload['required_rd_ratio_from_bao']:.6g}",
            f"- residual: {payload['ratio_residual']:.6g}",
            f"- required Delta N_eff for target: {payload['required_delta_neff_for_bao_ratio']:.6g}",
            f"- Delta N_eff shortfall: {payload['delta_neff_shortfall']:.6g}",
            "",
            "## Next",
            "",
            payload["next_required"],
            "",
        ]
    )


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
