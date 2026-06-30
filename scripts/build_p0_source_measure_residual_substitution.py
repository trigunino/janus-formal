from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_source_measure_residual_substitution.md")
JSON_PATH = Path("outputs/reports/p0_source_measure_residual_substitution.json")


def build_payload() -> dict:
    substitutions = [
        {
            "branch": "field_equation_4volume_source",
            "r_plus_source": "D_plus_nu(B_4vol_plus_from_minus K_plus^{mu nu})",
            "r_minus_source": "D_minus_nu(B_4vol_minus_from_plus K_minus^{mu nu})",
            "expanded_terms": [
                "B_4vol D K",
                "K D log B_4vol",
                "D L terms inside D K",
                "connection-difference force terms",
            ],
            "open_obstruction": "D log B_4vol and D L must cancel from source equations",
        },
        {
            "branch": "slice_dust_flux_source",
            "r_plus_source": "D_plus_nu(V3_dust_plus_from_minus rho_minus u_-to+^mu u_-to+^nu)",
            "r_minus_source": "D_minus_nu(V3_dust_minus_from_plus rho_plus u_+to-^mu u_+to-^nu)",
            "expanded_terms": [
                "V3_dust transported continuity",
                "rho u u D log V3_dust",
                "lapse reinsertion residual",
                "D L terms inside transported velocities",
            ],
            "open_obstruction": "slice-to-4D reinsertion must recover the field-equation residual",
        },
        {
            "branch": "effective_density_source",
            "r_plus_source": "D_plus_nu(rho_eff_plus_from_minus u_-to+^mu u_-to+^nu)",
            "r_minus_source": "D_minus_nu(rho_eff_minus_from_plus u_+to-^mu u_+to-^nu)",
            "expanded_terms": [
                "D rho_eff",
                "rho_eff transported force",
                "declared absorbed-measure derivative",
                "no extra Q_det multiplication",
            ],
            "open_obstruction": "rho_eff must declare and carry exactly one absorbed measure",
        },
    ]
    required_zero_conditions = [
        "R_plus residual row equals zero after expansion",
        "R_minus residual row equals zero after expansion",
        "the same L used by K appears in Q_cross",
        "pressure metric/projector and Pi terms remain explicit tensor terms",
        "no branch mixes B_4vol, V3_dust, and rho_eff in the same source",
    ]
    return {
        "description": "P0 substitution table for source-measure branches inside R_plus/R_minus.",
        "status": "substitution-written-residuals-open",
        "substitution_rows_written": True,
        "residual_terms_expanded": True,
        "accepted_branch": None,
        "r_plus_closed": False,
        "r_minus_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "substitutions": substitutions,
        "required_zero_conditions": required_zero_conditions,
        "verdict": (
            "The residual substitutions are explicit enough to reject scalar shortcuts. "
            "They do not close Janus until one branch proves every required zero condition."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Source-Measure Residual Substitution",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Accepted branch: {payload['accepted_branch']}",
        f"R_plus closed: {payload['r_plus_closed']}",
        f"R_minus closed: {payload['r_minus_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Substitutions",
        "",
    ]
    for row in payload["substitutions"]:
        lines.append(f"- {row['branch']}:")
        lines.append(f"  - R_plus source: `{row['r_plus_source']}`")
        lines.append(f"  - R_minus source: `{row['r_minus_source']}`")
        lines.append(f"  - expanded terms: {', '.join(row['expanded_terms'])}")
        lines.append(f"  - open obstruction: {row['open_obstruction']}")
    lines.extend(["", "## Required Zero Conditions", ""])
    lines.extend(f"- {item}" for item in payload["required_zero_conditions"])
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
