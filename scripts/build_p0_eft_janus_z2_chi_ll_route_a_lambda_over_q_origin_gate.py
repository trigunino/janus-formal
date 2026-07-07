from __future__ import annotations

import json
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
INPUT_PATH = BASE / "lambda_over_q_origin_inputs.json"
WILL_RADIUS_OUTPUT = BASE / "will_flux_radius_inputs.json"
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_chi_ll_route_a_lambda_over_q_origin_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_chi_ll_route_a_lambda_over_q_origin_gate.json"
)

FORBIDDEN_TOKENS = ("fit", "planck", "lcdm", "bao", "z4", "demo")


def _read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def _bad_provenance(value: Any) -> bool:
    text = str(value or "").strip().lower()
    return not text or any(token in text for token in FORBIDDEN_TOKENS)


def _positive(data: dict[str, Any], key: str) -> float | None:
    value = data.get(key)
    if isinstance(value, (int, float)) and float(value) > 0.0:
        return float(value)
    return None


def build_payload(
    input_path: Path = INPUT_PATH,
    will_radius_output: Path = WILL_RADIUS_OUTPUT,
    *,
    write_output: bool = False,
) -> dict[str, Any]:
    data = _read(input_path)
    ratio = _positive(data, "lambda_F2_over_q_LL_m_minus_2")
    n_flux = data.get("flux_integer_n")
    origin = data.get("origin_route")

    origin_checks = {
        "canonical_connection_normalization": {
            "selected": origin == "canonical_connection_normalization",
            "required": [
                "A_LL_is_connection_on_global_U1_bundle",
                "minimal_charge_unit_derived",
                "WILL_lambda_normalization_derived",
            ],
            "ready": all(
                bool(data.get(key))
                for key in [
                    "A_LL_is_connection_on_global_U1_bundle",
                    "minimal_charge_unit_derived",
                    "WILL_lambda_normalization_derived",
                ]
            ),
        },
        "PT_Noether_boundary_charge": {
            "selected": origin == "PT_Noether_boundary_charge",
            "required": [
                "PT_boundary_symplectic_potential_projected",
                "Noether_charge_unit_derived",
                "charge_to_LL_connection_map_derived",
                "PT_Noether_radius_or_mass_charge_derived",
            ],
            "ready": all(
                bool(data.get(key))
                for key in [
                    "PT_boundary_symplectic_potential_projected",
                    "Noether_charge_unit_derived",
                    "charge_to_LL_connection_map_derived",
                    "PT_Noether_radius_or_mass_charge_derived",
                ]
            ),
        },
        "UV_action_dimensional_coupling": {
            "selected": origin == "UV_action_dimensional_coupling",
            "required": [
                "UV_length_or_mass_scale_derived",
                "lambda_F2_from_UV_action_derived",
                "q_LL_from_same_UV_sector_derived",
            ],
            "ready": all(
                bool(data.get(key))
                for key in [
                    "UV_length_or_mass_scale_derived",
                    "lambda_F2_from_UV_action_derived",
                    "q_LL_from_same_UV_sector_derived",
                ]
            ),
        },
    }
    selected_ready = any(item["selected"] and item["ready"] for item in origin_checks.values())
    required_conditions = {
        "origin_route_declared": origin in origin_checks,
        "lambda_F2_over_q_LL_available": ratio is not None,
        "flux_integer_n_available": isinstance(n_flux, int) and n_flux != 0,
        "physical_area_gauge": data.get("area_gauge") == "physical_induced_S2_metric",
        "non_observational_provenance": not _bad_provenance(data.get("provenance")),
        "selected_origin_route_ready": selected_ready,
    }
    ready = all(required_conditions.values())
    will_payload = None
    if ready:
        will_payload = {
            "flux_integer_n": n_flux,
            "lambda_F2_over_q_LL": ratio,
            "area_gauge": "physical_induced_S2_metric",
            "non_observational_provenance": True,
            "power_p": 0.5,
            "source": f"route_a_lambda_over_q:{origin}",
        }
        if write_output:
            will_radius_output.parent.mkdir(parents=True, exist_ok=True)
            will_radius_output.write_text(json.dumps(will_payload, indent=2), encoding="utf-8")

    return {
        "status": "janus-z2-chi-ll-route-a-lambda-over-q-origin-gate",
        "active_core": "Z2_tunnel_Sigma_null_PT_bridge",
        "physical_statement": (
            "Route A can close only if the invariant ratio lambda_F2/q_LL is "
            "derived from one coherent Janus/PT origin: canonical U(1) charge "
            "normalization, PT/Noether boundary charge, or a dimensionful UV "
            "action coupling. The ratio may then feed the WILL flux-radius map."
        ),
        "input_path": str(input_path),
        "input_present": input_path.exists(),
        "will_radius_output": str(will_radius_output),
        "origin_checks": origin_checks,
        "required_conditions": required_conditions,
        "lambda_F2_over_q_LL_m_minus_2": ratio,
        "will_flux_radius_payload": will_payload,
        "route_a_origin_ready": ready,
        "chi_LL_prediction_ready": ready,
        "blocked_by": [key for key, value in required_conditions.items() if not value],
        "forbidden_shortcuts": [
            "set_lambda_over_q_by_observation",
            "mix_lambda_from_one_sector_with_q_from_another_sector",
            "absorb_q_LL_into_flux_integer_after_c1_quantization",
            "reuse_legacy_Z4_normalization",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload(write_output=True)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 chi_LL Route A lambda_F2/q_LL Origin Gate",
        "",
        payload["physical_statement"],
        "",
        f"Route A origin ready: `{payload['route_a_origin_ready']}`",
        f"lambda_F2/q_LL: `{payload['lambda_F2_over_q_LL_m_minus_2']}`",
        "",
        "## Blocked By",
    ]
    lines.extend(f"- `{item}`" for item in payload["blocked_by"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
