from __future__ import annotations

import json
import math
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_area_superselection_sector_manifest import (
    INPUT_PATH as SUPERSELECTION_INPUT,
    build_payload as area_superselection,
)


BASE = Path("outputs/active_z2_sigma")
INPUT_PATH = BASE / "sigma_discrete_family_propagation_inputs.json"
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_discrete_family_propagation.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_discrete_family_propagation.json")

C_SI = 299_792_458.0
G_SI = 6.674_30e-11
MPC_M = 3.085_677_581_491_367e22

FORBIDDEN_TOKENS = ("fit", "planck", "lcdm", "bao", "z4", "demo")


def _read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def _bad_provenance(value: Any) -> bool:
    text = str(value or "").strip().lower()
    return not text or any(token in text for token in FORBIDDEN_TOKENS)


def _flux_integer(value: Any) -> int | None:
    return value if isinstance(value, int) and value != 0 else None


def _positive_number(value: Any) -> float | None:
    if not isinstance(value, (int, float)):
        return None
    value = float(value)
    return value if math.isfinite(value) and value > 0 else None


def _augment_sector(entry: dict[str, Any], *, n_flux: int | None, g_eff: float) -> dict[str, Any]:
    radius = float(entry["R_s_m"])
    chi_abs_inverse = float(entry["chi_LL_abs_inverse_m"])
    mass = C_SI**2 * radius / (2.0 * g_eff)
    out = {
        **entry,
        "chi_LL_sign": "negative_PT_branch",
        "M_bridge_kg": mass,
        "M_bridge_geometrized_m": radius / 2.0,
        "spectral_scale_inverse_m": 1.0 / radius,
        "spectral_scale_hz": C_SI / radius,
        "H_equivalent_km_s_Mpc": (C_SI / radius) * (MPC_M / 1000.0),
    }
    if n_flux is not None:
        out["flux_integer_n"] = n_flux
        out["lambda_F2_over_q_LL_m_minus_2"] = radius * radius / (
            math.sqrt(8.0) * abs(n_flux)
        )
    out["chi_LL_abs_inverse_m"] = chi_abs_inverse
    return out


def build_payload(
    input_path: Path = INPUT_PATH,
    superselection_input: Path = SUPERSELECTION_INPUT,
) -> dict[str, Any]:
    data = _read(input_path)
    super_input = Path(data.get("superselection_input_path", str(superselection_input)))
    super_payload = area_superselection(super_input)
    n_flux = _flux_integer(data.get("flux_integer_n"))
    g_eff = _positive_number(data.get("G_eff_SI")) or G_SI
    conditions = {
        "area_superselection_family_ready": super_payload["superselection_family_ready"],
        "non_observational_provenance": not _bad_provenance(data.get("provenance")),
    }
    ready = all(conditions.values())
    table = []
    if ready:
        table = [_augment_sector(item, n_flux=n_flux, g_eff=g_eff) for item in super_payload["sector_table"]]
    return {
        "status": "janus-z2-sigma-discrete-family-propagation",
        "active_core": "Z2_tunnel_Sigma_null_PT_bridge",
        "physical_statement": (
            "Propagates the discrete N_gap superselection family to R_s, chi_LL, "
            "bridge mass, spectral scale and optional LL flux normalization. It "
            "does not select a sector."
        ),
        "input_path": str(input_path),
        "input_present": input_path.exists(),
        "superselection_input_path": str(super_input),
        "conditions": conditions,
        "formulae": {
            "chi_LL": "-1/(8*pi*R_s)",
            "M_bridge": "c^2*R_s/(2*G_eff)",
            "lambda_over_q_if_flux_given": "R_s^2/(sqrt(8)*|n|)",
            "spectral_scale": "1/R_s",
        },
        "flux_integer_n": n_flux,
        "sector_table": table,
        "discrete_family_propagation_ready": ready,
        "unique_prediction_ready": False,
        "blocked_by": [key for key, ok in conditions.items() if not ok],
        "forbidden_shortcuts": [
            "choose_sector_by_observation",
            "collapse_superselection_family_to_unique_prediction",
            "infer_N_gap_equals_abs_n_after_negative_closure_audit",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Sigma Discrete Family Propagation",
        "",
        payload["physical_statement"],
        "",
        f"Propagation ready: `{payload['discrete_family_propagation_ready']}`",
        f"Unique prediction ready: `{payload['unique_prediction_ready']}`",
        "",
        "## Sectors",
    ]
    for item in payload["sector_table"]:
        lines.append(
            f"- N_gap={item['N_gap']}: R_s={item['R_s_m']} m, "
            f"M_bridge={item['M_bridge_kg']} kg"
        )
    lines.append("")
    lines.append("## Blocked By")
    lines.extend(f"- `{item}`" for item in payload["blocked_by"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
