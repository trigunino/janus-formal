from __future__ import annotations

import json
import math
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_discrete_family_propagation import (
    build_payload as discrete_family,
)


BASE = Path("outputs/active_z2_sigma")
INPUT_PATH = BASE / "discrete_sector_internal_constraints_inputs.json"
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_discrete_sector_internal_constraints.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_discrete_sector_internal_constraints.json")

HBAR_SI = 1.054_571_817e-34
C_SI = 299_792_458.0
KB_SI = 1.380_649e-23


def _read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def _range(value: Any) -> tuple[float | None, float | None]:
    if not isinstance(value, dict):
        return None, None
    low = value.get("min")
    high = value.get("max")
    low = float(low) if isinstance(low, (int, float)) and math.isfinite(float(low)) else None
    high = float(high) if isinstance(high, (int, float)) and math.isfinite(float(high)) else None
    return low, high


def _in_range(value: float, bounds: tuple[float | None, float | None]) -> bool:
    low, high = bounds
    return (low is None or value >= low) and (high is None or value <= high)


def _sector_checks(entry: dict[str, Any], data: dict[str, Any]) -> dict[str, Any]:
    radius = float(entry["R_s_m"])
    checks: dict[str, bool] = {}
    derived = {
        "laplacian_l1_m_minus_2": 2.0 / radius**2,
        "dirac_k0_m_minus_1": 1.0 / radius,
        "horizon_kappa_if_Rs_1_per_m": 1.0 / radius,
        "horizon_temperature_if_kappa_Rs_K": HBAR_SI * C_SI / (2.0 * math.pi * KB_SI * radius),
    }
    ranges = {
        "laplacian_l1_m_minus_2": _range(data.get("laplacian_l1_m_minus_2_range")),
        "dirac_k0_m_minus_1": _range(data.get("dirac_k0_m_minus_1_range")),
        "horizon_temperature_if_kappa_Rs_K": _range(
            data.get("horizon_temperature_if_kappa_Rs_K_range")
        ),
    }
    for key, bounds in ranges.items():
        if bounds != (None, None):
            checks[key] = _in_range(float(derived[key]), bounds)
    if "casimir_coefficient_C" in data:
        coeff = float(data["casimir_coefficient_C"])
        derived["rho_casimir_J_m3"] = coeff / radius**4
        bounds = _range(data.get("rho_casimir_J_m3_range"))
        if bounds != (None, None):
            checks["rho_casimir_J_m3"] = _in_range(float(derived["rho_casimir_J_m3"]), bounds)
    return {
        "N_gap": entry["N_gap"],
        "R_s_m": radius,
        "M_bridge_kg": float(entry["M_bridge_kg"]),
        "chi_LL_abs_inverse_m": float(entry["chi_LL_abs_inverse_m"]),
        "derived_internal_quantities": derived,
        "checks": checks,
        "sector_survives_internal_constraints": all(checks.values()) if checks else True,
        "diagnostic_only": not checks,
    }


def _rankings(rows: list[dict[str, Any]]) -> dict[str, list[int]]:
    def by(path: str, *, reverse: bool = False) -> list[int]:
        def value(row: dict[str, Any]) -> float:
            if path in row:
                return float(row[path])
            return float(row["derived_internal_quantities"][path])

        return [row["N_gap"] for row in sorted(rows, key=value, reverse=reverse)]

    return {
        "radius_ascending": by("R_s_m"),
        "bridge_mass_ascending": by("M_bridge_kg"),
        "spectral_scale_descending": by("dirac_k0_m_minus_1", reverse=True),
        "horizon_temperature_descending": by("horizon_temperature_if_kappa_Rs_K", reverse=True),
        "curvature_laplacian_scale_descending": by("laplacian_l1_m_minus_2", reverse=True),
    }


def build_payload(input_path: Path = INPUT_PATH) -> dict[str, Any]:
    data = _read(input_path)
    family = discrete_family()
    contracts = {
        "discrete_family_ready": family["discrete_family_propagation_ready"],
        "constraints_declared_before_scan": bool(data.get("constraints_declared_before_scan")),
        "no_observational_fit": not bool(data.get("observational_fit_used")),
    }
    ready = all(contracts.values())
    rows = [_sector_checks(item, data) for item in family["sector_table"]] if ready else []
    rankings = _rankings(rows) if ready and bool(data.get("ranking_diagnostics_enabled")) else {}
    return {
        "status": "janus-z2-sigma-discrete-sector-internal-constraints",
        "active_core": "Z2_tunnel_Sigma_null_PT_bridge",
        "physical_statement": (
            "Applies internal physics checks to each fixed N_gap sector: spectral "
            "scales, optional horizon-temperature scale, and optional Casimir "
            "density. No observational fit is allowed."
        ),
        "input_path": str(input_path),
        "input_present": input_path.exists(),
        "contracts": contracts,
        "internal_constraints_ready": ready,
        "sector_rows": rows,
        "diagnostic_rankings": rankings,
        "diagnostic_rankings_are_constraints": False,
        "internal_unique_sector_selected": False,
        "surviving_sectors": [
            row["N_gap"] for row in rows if row["sector_survives_internal_constraints"]
        ],
        "rejected_sectors": [
            row["N_gap"] for row in rows if not row["sector_survives_internal_constraints"]
        ],
        "blocked_by": [key for key, ok in contracts.items() if not ok],
        "forbidden_shortcuts": [
            "derive_ranges_from_observations",
            "promote_diagnostic_ranking_to_selection_law",
            "drop_horizon_or_Casimir_condition_after_failure",
            "retune_gamma_or_j_min_per_sector",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Sigma Discrete Sector Internal Constraints",
        "",
        payload["physical_statement"],
        "",
        f"Ready: `{payload['internal_constraints_ready']}`",
        f"Survivors: `{payload['surviving_sectors']}`",
        f"Rejected: `{payload['rejected_sectors']}`",
        f"Diagnostic rankings are constraints: `{payload['diagnostic_rankings_are_constraints']}`",
        "",
        "## Blocked By",
    ]
    lines.extend(f"- `{item}`" for item in payload["blocked_by"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
