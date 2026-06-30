from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_pulled_dust_el_projection_substitution.md")
JSON_PATH = Path("outputs/reports/p0_pulled_dust_el_projection_substitution.json")


def build_payload() -> dict:
    substitution_rows = [
        {
            "piece": "measure_density",
            "source": "delta(B rho)",
            "target": "cancels by Jacobian/volume/DlogB identities",
            "depends_on": "p0_stueckelberg_dphi_density_cancellation",
            "closed": False,
        },
        {
            "piece": "velocity_tetrad",
            "source": "delta_L u and transported tetrad variation",
            "target": "localizes D_L velocity/tetrad terms",
            "depends_on": "p0_stueckelberg_dl_velocity_cancellation",
            "closed": False,
        },
        {
            "piece": "transverse_force",
            "source": "remaining transverse EL projection",
            "target": "rho h C(u,u)",
            "depends_on": "p0_stueckelberg_projected_cuu_map_force_balance",
            "closed": False,
        },
        {
            "piece": "mirror_inverse",
            "source": "same phi/L inverse map",
            "target": "minus identity follows from inverse convention",
            "depends_on": "p0_stueckelberg_phi_l_convention_lock",
            "closed": False,
        },
    ]
    sufficient_conditions = [
        "measure_density closed",
        "velocity_tetrad closed",
        "transverse_force derived from EL projection, not imposed",
        "mirror_inverse closed with one phi/L convention",
        "pressure/Pi excluded from dust claim or separately transported",
    ]
    return {
        "description": "Substitution ledger for pulled dust EL projection into rho h Cuu.",
        "status": "el-projection-substitution-open",
        "substitution_rows": substitution_rows,
        "sufficient_conditions": sufficient_conditions,
        "all_substitutions_closed": False,
        "projected_cuu_from_el_closed": False,
        "conditional_dust_branch_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The pulled dust EL projection is decomposed into finite pieces. Closure "
            "requires closing every row; no weak-congruence or transverse-multiplier shortcut is allowed."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Pulled Dust EL Projection Substitution",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"All substitutions closed: {payload['all_substitutions_closed']}",
        f"Projected Cuu from EL closed: {payload['projected_cuu_from_el_closed']}",
        f"Conditional dust branch closed: {payload['conditional_dust_branch_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| piece | source | target | depends on | closed |",
        "|---|---|---|---|---|",
    ]
    for row in payload["substitution_rows"]:
        lines.append(
            f"| {row['piece']} | {row['source']} | {row['target']} | "
            f"`{row['depends_on']}` | {row['closed']} |"
        )
    lines.extend(["", "## Sufficient Conditions", ""])
    lines.extend(f"- {item}" for item in payload["sufficient_conditions"])
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.parent.mkdir(parents=True, exist_ok=True)
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
