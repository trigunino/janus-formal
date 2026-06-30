from __future__ import annotations

from fractions import Fraction
from pathlib import Path
import json
import os


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))
REPORT_PATH = REPORT_DIR / "p0_linear_growth_early_structure_map.md"
JSON_PATH = REPORT_DIR / "p0_linear_growth_early_structure_map.json"


FORMULAS = {
    "growth_equation": "delta'' + A(a)*delta' - S_eff(a)*delta = 0",
    "friction_index": "A(a) = 2 + dln H / dln a",
    "effective_source": "S_eff(a) = G_eff^+ rho_plus + C_rep rho_DM_app",
    "growth_boost": "S_eff(a)/S_GR(a)",
    "collapse_time_index": "S_GR(a)/S_eff(a)",
}


def growth_source_strength(rho_plus: int, rho_dm: int, g_eff: int, c_rep: int) -> int:
    return g_eff * rho_plus + c_rep * rho_dm


def sample_witness() -> dict:
    params = {
        "Mpl2": 4,
        "mHR2": 1,
        "T_memb": 30,
        "v": 1,
        "rho_plus": 2,
        "rho_minus": 5,
        "a_plus": 1,
        "a_minus": 2,
        "dlnH_dln a": Fraction(-1, 2),
        "G_eff_plus": 1,
        "C_rep": 1,
        "S_GR": 2,
    }

    rho_dm = Fraction(params["a_minus"] ** 3, params["a_plus"] ** 3) * params["rho_minus"]
    s_eff = growth_source_strength(
        params["rho_plus"], int(rho_dm), params["G_eff_plus"], params["C_rep"]
    )
    growth_boost = Fraction(s_eff, params["S_GR"])
    collapse_time = Fraction(params["S_GR"], s_eff)

    return {
        "params": params,
        "formulas": {
            "rho_DM_app": str(rho_dm),
            "S_eff": str(s_eff),
            "growth_boost": str(growth_boost),
            "collapse_time_index": str(collapse_time),
        },
    }


def build_payload() -> dict:
    witness = sample_witness()
    return {
        "description": (
            "Linear-growth/JWST gate extracted from the same candidate FLRW "
            "background and exact scalar/vector sector frontiers."
        ),
        "status": "linear_growth_gate_closed_conditionally",
        "micro_theory_ready": True,
        "flrw_gate_closed": True,
        "dark_sector_gate_closed": True,
        "hubble_gate_closed": False,
        "structure_gate_closed": True,
        "falsifiable_signatures_open": [
            "negative-lensing divergence signature",
            "primordial-GW transition spectrum",
        ],
        "formulas": FORMULAS,
        "sample_witness": witness,
        "source_derivation_constraints": [
            "growth equation from SVT-drifted quadratic truncation",
            "collapse-time index derived from effective source strength",
            "JWST early-collapse written as falsifiable output",
        ],
        "frontier_check": {
            "aether_not_reintroduced": True,
            "same_action_parameters": "required",
            "vector_mass": "vector_alpha>0 by M_pl^2 v - aetherKineticScale v > 0",
            "scalar_mass": "scalar_alpha>0 by 2*lambdaPhi v^2 + vector_alpha > 0",
        },
        "remaining_blocks": [
            "derive signatures that differ from GR/Lambda-CDM",
            "add primordial-GW transition diagnostics",
            "connect to likelihood without ad-hoc fitting",
        ],
        "next_gate": "derive_negative_lensing_and_primordial_gw_signatures",
        "observable_prediction_ready": False,
        "reason_not_ready": (
            "Early-structure/JWST gate is conditionally closed, but the falsifiable "
            "signature block and likelihood pipeline are still open."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Linear Growth / Early Structure Map",
        "",
        payload["description"],
        "",
        f"Status: `{payload['status']}`",
        f"Structure gate closed: `{payload['structure_gate_closed']}`",
        f"Observable prediction ready: `{payload['observable_prediction_ready']}`",
        "",
        "## Source Formulas",
        "",
    ]
    for key, value in payload["formulas"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend([
        "",
        "## Sample Witness",
        "",
        f"- params: `{payload['sample_witness']['params']}`",
    ])
    for key, value in payload["sample_witness"]["formulas"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend([
        "",
        "## Frontier Checks",
        "",
    ])
    for key, value in payload["frontier_check"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Remaining blocks", ""])
    for block in payload["remaining_blocks"]:
        lines.append(f"- {block}")
    return "\n".join(lines)


def write_reports(
    report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH
) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    json_path.write_text(json.dumps(payload, indent=2, default=str), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
