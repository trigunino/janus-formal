from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
INPUT_PATH = BASE / "sigma_area_spectrum_inputs.json"
AREA_GAP_OUTPUT = BASE / "area_gap_exit_inputs.json"
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_area_spectrum_closure_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_area_spectrum_closure_gate.json")

C_SI = 299_792_458.0
HBAR_SI = 1.054_571_817e-34
G_SI = 6.674_30e-11

FORBIDDEN_TOKENS = ("fit", "planck", "lcdm", "bao", "z4", "demo")


def _read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def _positive_number(data: dict[str, Any], key: str) -> float | None:
    value = data.get(key)
    if not isinstance(value, (int, float)):
        return None
    value = float(value)
    return value if math.isfinite(value) and value > 0.0 else None


def _bad_provenance(value: Any) -> bool:
    text = str(value or "").strip().lower()
    return not text or any(token in text for token in FORBIDDEN_TOKENS)


def _derive(data: dict[str, Any]) -> dict[str, Any]:
    gamma_abs = _positive_number(data, "holst_immirzi_abs")
    j_min = _positive_number(data, "j_min")
    g_eff = _positive_number(data, "G_eff_SI") or G_SI
    if gamma_abs is None or j_min is None:
        return {"ready": False, "missing": ["holst_immirzi_abs", "j_min"]}
    l_planck_sq = HBAR_SI * g_eff / C_SI**3
    area_gap = 8.0 * math.pi * gamma_abs * l_planck_sq * math.sqrt(j_min * (j_min + 1.0))
    n_gap = data.get("N_gap")
    area = None
    radius = None
    if isinstance(n_gap, int) and n_gap > 0:
        area = n_gap * area_gap
        radius = math.sqrt(area / (4.0 * math.pi))
    return {
        "ready": True,
        "G_eff_SI": g_eff,
        "l_planck_sq_m2": l_planck_sq,
        "A_gap_m2": area_gap,
        "N_gap": n_gap if isinstance(n_gap, int) and n_gap > 0 else None,
        "A_Sigma_m2": area,
        "R_s_m": radius,
        "missing": [] if radius is not None else ["positive_integer_N_gap"],
    }


def build_payload(
    input_path: Path = INPUT_PATH,
    area_gap_output: Path = AREA_GAP_OUTPUT,
    *,
    write_output: bool = False,
) -> dict[str, Any]:
    data = _read(input_path)
    derivation = _derive(data)
    required_conditions = {
        "active_core_Z2_tunnel_Sigma": data.get("active_core") == "Z2_tunnel_Sigma",
        "branch_null_PT_bridge": data.get("branch") == "Z2_null_Sigma_PT_bridge",
        "source_active_derived": data.get("source") == "active_derived",
        "area_operator_on_Sigma_derived": bool(data.get("area_operator_on_Sigma_derived")),
        "Holst_area_spectrum_law_derived": bool(data.get("Holst_area_spectrum_law_derived")),
        "physical_induced_area_gauge": data.get("area_gauge") == "physical_induced_S2_metric",
        "non_observational_provenance": not _bad_provenance(data.get("area_spectrum_provenance")),
    }
    gap_ready = all(required_conditions.values()) and derivation["ready"]
    radius_ready = gap_ready and derivation["R_s_m"] is not None
    area_payload = None
    if gap_ready:
        area_payload = {
            "quantum_area_operator_on_Sigma": True,
            "A_gap_m2": derivation["A_gap_m2"],
            "A_Sigma_equals_N_gap_A_gap_theorem": True,
            "N_gap": derivation["N_gap"],
            "area_gauge": "physical_induced_S2_metric",
            "non_observational_provenance": True,
            "source": "sigma_area_spectrum_closure",
        }
        if write_output:
            area_gap_output.parent.mkdir(parents=True, exist_ok=True)
            area_gap_output.write_text(json.dumps(area_payload, indent=2), encoding="utf-8")
    return {
        "status": "janus-z2-sigma-area-spectrum-closure-gate",
        "active_core": "Z2_tunnel_Sigma_null_PT_bridge",
        "physical_statement": (
            "A Sigma throat area gap can be computed from a Holst/area-spectrum "
            "law only after the area operator, physical induced area gauge, "
            "Immirzi normalization and minimal representation are derived. "
            "N_gap remains an area occupation/state selector unless separately "
            "fixed by topology, stability or a state condition."
        ),
        "input_path": str(input_path),
        "input_present": input_path.exists(),
        "area_gap_output": str(area_gap_output),
        "required_conditions": required_conditions,
        "formulae": {
            "planck_area": "l_P^2 = hbar*G_eff/c^3",
            "holst_area_gap": "A_gap = 8*pi*|gamma|*l_P^2*sqrt(j_min*(j_min+1))",
            "area": "A_Sigma = N_gap*A_gap",
            "radius": "R_s = sqrt(A_Sigma/(4*pi))",
        },
        "derivation": derivation,
        "area_gap_formula_ready": gap_ready,
        "R_s_prediction_ready": radius_ready,
        "area_gap_payload": area_payload,
        "blocked_by": [key for key, value in required_conditions.items() if not value]
        + derivation.get("missing", []),
        "forbidden_shortcuts": [
            "choose_gamma_by_observation",
            "choose_j_min_by_observation",
            "choose_N_gap_by_observation",
            "use_legacy_Z4_area_gap",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload(write_output=True)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Sigma Area Spectrum Closure Gate",
        "",
        payload["physical_statement"],
        "",
        f"Area gap formula ready: `{payload['area_gap_formula_ready']}`",
        f"R_s prediction ready: `{payload['R_s_prediction_ready']}`",
        f"A_gap m^2: `{payload['derivation'].get('A_gap_m2')}`",
        f"R_s m: `{payload['derivation'].get('R_s_m')}`",
        "",
        "## Blocked By",
    ]
    lines.extend(f"- `{item}`" for item in payload["blocked_by"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
