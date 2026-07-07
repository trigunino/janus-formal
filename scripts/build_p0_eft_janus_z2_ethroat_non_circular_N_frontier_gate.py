from __future__ import annotations

import json
from pathlib import Path


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_z2_ethroat_non_circular_N_frontier_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_z2_ethroat_non_circular_N_frontier_gate.md"


FORBIDDEN_INPUTS = {"H0", "L", "R_H", "A_H", "alpha", "observed_Lambda"}


def _route(name: str, formula: str, inputs: list[str], gives_target: bool, note: str) -> dict:
    circular_inputs = sorted(set(inputs) & FORBIDDEN_INPUTS)
    return {
        "name": name,
        "formula": formula,
        "inputs": inputs,
        "gives_N_1e120": gives_target,
        "circular_inputs": circular_inputs,
        "non_circular": not circular_inputs,
        "accepted_selector": gives_target and not circular_inputs,
        "note": note,
    }


def build_payload() -> dict:
    routes = {
        "horizon_entropy": _route(
            "horizon_entropy",
            "N = A_H/(4 lP^2)",
            ["A_H", "H0"],
            True,
            "gets the right number but is exactly the target scale written as entropy",
        ),
        "uv_ir_ratio": _route(
            "uv_ir_ratio",
            "N = (L/lP)^2",
            ["L"],
            True,
            "same quantity as the candidate area law; not an independent selector",
        ),
        "cosmological_constant_ratio": _route(
            "cosmological_constant_ratio",
            "N = 1/(Lambda*lP^2)",
            ["observed_Lambda"],
            True,
            "right order, but imports the observed late-time scale",
        ),
        "euler_characteristic": _route(
            "euler_characteristic",
            "N = F(chi(S4), chi(RP4), cover_degree)",
            ["topology"],
            False,
            "non-circular but produces O(1), not 10^120",
        ),
        "pin_holonomy_order": _route(
            "pin_holonomy_order",
            "N = order(holonomy or lifted monodromy)",
            ["topology", "Pin_lift"],
            False,
            "non-circular but bounded by small group/order data",
        ),
        "species_count": _route(
            "species_count",
            "N = N_species * N_modes",
            ["field_content", "mode_cutoff"],
            False,
            "could be large, but Janus does not derive field content or cutoff count",
        ),
        "microcanonical_state_count": _route(
            "microcanonical_state_count",
            "N = log dim H_Sigma",
            ["boundary_Hilbert_space", "state_law"],
            False,
            "this is the most plausible non-circular route, but Hilbert space and state law are not derived",
        ),
        "topological_qft_partition_function": _route(
            "topological_qft_partition_function",
            "N = log Z_TQFT(Sigma)",
            ["TQFT_choice", "level_k"],
            False,
            "non-circular only if TQFT and level follow from Janus; currently new theory input",
        ),
    }
    accepted = [name for name, route in routes.items() if route["accepted_selector"]]
    plausible_non_circular_frontiers = [
        name
        for name, route in routes.items()
        if route["non_circular"] and name in {"microcanonical_state_count", "topological_qft_partition_function"}
    ]
    return {
        "status": "janus-z2-ethroat-non-circular-N-frontier-gate",
        "active_core": "S4_L_to_RP4_L_resolved_by_Sigma",
        "target_N": "O(10^120)",
        "forbidden_circular_inputs": sorted(FORBIDDEN_INPUTS),
        "routes": routes,
        "accepted_non_circular_selectors": accepted,
        "N_selected_non_circularly": bool(accepted),
        "best_remaining_frontiers": plausible_non_circular_frontiers,
        "frontier_verdict": (
            "No current non-circular route selects N~10^120. The only plausible "
            "non-circular frontiers are a Janus-derived boundary Hilbert-space "
            "state-counting law or a Janus-derived TQFT/level on Sigma."
        ),
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 E_throat Non-Circular N Frontier Gate",
        "",
        f"Target N: `{payload['target_N']}`",
        f"N selected non-circularly: `{payload['N_selected_non_circularly']}`",
        f"Accepted selectors: `{payload['accepted_non_circular_selectors']}`",
        f"Best remaining frontiers: `{payload['best_remaining_frontiers']}`",
        "",
        "## Routes",
    ]
    for name, route in payload["routes"].items():
        lines.append(
            f"- `{name}`: gives_target=`{route['gives_N_1e120']}`, "
            f"non_circular=`{route['non_circular']}`; {route['note']}"
        )
    lines.extend(["", "## Verdict", "", payload["frontier_verdict"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
