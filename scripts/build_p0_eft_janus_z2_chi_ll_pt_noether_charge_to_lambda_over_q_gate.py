from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
INPUT_PATH = BASE / "pt_noether_charge_to_lambda_over_q_inputs.json"
ROUTE_A_OUTPUT = BASE / "lambda_over_q_origin_inputs.json"
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_chi_ll_pt_noether_charge_to_lambda_over_q_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_chi_ll_pt_noether_charge_to_lambda_over_q_gate.json"
)

C_SI = 299_792_458.0
G_SI = 6.674_30e-11
FORBIDDEN_TOKENS = ("fit", "planck", "lcdm", "bao", "z4", "demo")


def _read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def _bad_provenance(value: Any) -> bool:
    text = str(value or "").strip().lower()
    return not text or any(token in text for token in FORBIDDEN_TOKENS)


def _positive(data: dict[str, Any], key: str) -> float | None:
    value = data.get(key)
    if isinstance(value, (int, float)) and math.isfinite(float(value)) and float(value) > 0.0:
        return float(value)
    return None


def _derive_radius(data: dict[str, Any]) -> tuple[float | None, str | None]:
    radius = _positive(data, "R_s_m")
    if radius is not None:
        return radius, "R_s_m"
    mass = _positive(data, "M_bridge_kg")
    if mass is not None:
        return 2.0 * G_SI * mass / C_SI**2, "M_bridge_kg"
    energy = _positive(data, "Q_boundary_energy_J")
    if energy is not None:
        return 2.0 * G_SI * (energy / C_SI**2) / C_SI**2, "Q_boundary_energy_J"
    return None, None


def build_payload(
    input_path: Path = INPUT_PATH,
    route_a_output: Path = ROUTE_A_OUTPUT,
    *,
    write_output: bool = False,
) -> dict[str, Any]:
    data = _read(input_path)
    n_flux = data.get("flux_integer_n")
    radius, radius_source = _derive_radius(data)
    ratio = None
    if radius is not None and isinstance(n_flux, int) and n_flux != 0:
        # From WILL flux radius: R_s^4 = 8*n^2*(lambda_F2/q_LL)^2.
        ratio = radius * radius / (math.sqrt(8.0) * abs(int(n_flux)))

    required_conditions = {
        "PT_boundary_symplectic_potential_projected": bool(
            data.get("PT_boundary_symplectic_potential_projected")
        ),
        "Noether_charge_unit_derived": bool(data.get("Noether_charge_unit_derived")),
        "charge_to_LL_connection_map_derived": bool(
            data.get("charge_to_LL_connection_map_derived")
        ),
        "PT_energy_sign_reversal_proved": bool(data.get("PT_energy_sign_reversal_proved")),
        "radius_or_bridge_charge_available": radius is not None,
        "flux_integer_n_available": isinstance(n_flux, int) and n_flux != 0,
        "physical_area_gauge": data.get("area_gauge") == "physical_induced_S2_metric",
        "non_observational_provenance": not _bad_provenance(data.get("provenance")),
    }
    ready = all(required_conditions.values()) and ratio is not None
    route_a_payload = None
    if ready:
        route_a_payload = {
            "origin_route": "PT_Noether_boundary_charge",
            "PT_boundary_symplectic_potential_projected": True,
            "Noether_charge_unit_derived": True,
            "charge_to_LL_connection_map_derived": True,
            "lambda_F2_over_q_LL_m_minus_2": ratio,
            "flux_integer_n": int(n_flux),
            "area_gauge": "physical_induced_S2_metric",
            "provenance": f"active_pt_noether_boundary_charge:{data['provenance']}",
        }
        if write_output:
            route_a_output.parent.mkdir(parents=True, exist_ok=True)
            route_a_output.write_text(json.dumps(route_a_payload, indent=2), encoding="utf-8")

    return {
        "status": "janus-z2-chi-ll-pt-noether-charge-to-lambda-over-q",
        "active_core": "Z2_tunnel_Sigma_null_PT_bridge",
        "physical_statement": (
            "A PT/Noether boundary charge can feed Route A only after it gives "
            "an absolute bridge radius or mass/energy in the same PT boundary "
            "normalization as the LL connection. Then lambda_F2/q_LL follows "
            "from R_s^4=8*n^2*(lambda_F2/q_LL)^2."
        ),
        "input_path": str(input_path),
        "input_present": input_path.exists(),
        "route_a_output": str(route_a_output),
        "required_conditions": required_conditions,
        "radius_source": radius_source,
        "R_s_m": radius,
        "lambda_F2_over_q_LL_m_minus_2": ratio,
        "route_a_payload": route_a_payload,
        "pt_noether_lambda_over_q_ready": ready,
        "chi_LL_prediction_ready": ready,
        "formulae": {
            "mass_to_radius": "R_s = 2*G*M_bridge/c^2",
            "energy_to_radius": "R_s = 2*G*Q_boundary_energy/c^4",
            "ratio": "lambda_F2/q_LL = R_s^2/(sqrt(8)*|n|)",
        },
        "blocked_by": [key for key, value in required_conditions.items() if not value],
        "forbidden_shortcuts": [
            "use_total_cosmological_mass_as_bridge_mass_without_PT_projection",
            "use_boundary_charge_without_same_LL_connection_normalization",
            "set_bridge_mass_by_observation",
            "reuse_legacy_Z4_charge",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload(write_output=True)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 chi_LL PT/Noether Charge to lambda_F2/q_LL Gate",
        "",
        payload["physical_statement"],
        "",
        f"Ready: `{payload['pt_noether_lambda_over_q_ready']}`",
        f"R_s m: `{payload['R_s_m']}`",
        f"lambda_F2/q_LL: `{payload['lambda_F2_over_q_LL_m_minus_2']}`",
        "",
        "## Blocked By",
    ]
    lines.extend(f"- `{item}`" for item in payload["blocked_by"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
