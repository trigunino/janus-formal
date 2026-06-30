from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/qcross_covariant_projection_target.md")
JSON_PATH = Path("outputs/reports/qcross_covariant_projection_target.json")


def build_payload() -> dict:
    target = {
        "positive_optical_projection": "A_plus = (u_plus_mu k_plus^mu)^2",
        "negative_optical_projection": (
            "A_minus = (M_minus_to_plus[u_minus]_mu k_plus^mu)^2"
        ),
        "map_induction": "M_minus_to_plus is induced by admissible L_minus_to_plus, not by raw L_geom unless Lorentz compatibility is proved",
        "q_cross": "Q_cross = A_minus / A_plus",
        "dust_contraction": "T_s^{mu nu} k_plus_mu k_plus_nu = rho_s A_s",
        "perfect_fluid_contraction": (
            "T_s^{mu nu} k_plus_mu k_plus_nu = (rho_s + p_s) A_s"
        ),
    }
    reductions = [
        {
            "case": "equal_projection",
            "condition": "A_minus = A_plus",
            "result": "Q_cross = 1",
            "status": "current named convention",
        },
        {
            "case": "local_positive_orthonormal_frame",
            "condition": "u_plus=(1,0,0,0), k_plus=E(1,n), u_minus=gamma(1,beta)",
            "result": "Q_cross = gamma_minus^2 (1 - beta_vec.n)^2",
            "status": "implemented diagnostic reduction",
        },
        {
            "case": "raw_flrw_lapse",
            "condition": "coordinate-rest fluids compared without a derived cross-map",
            "result": "scale-factor lapse powers only",
            "status": "warning path, not admissible as prediction",
        },
    ]
    missing_maps = [
        "derive M_minus_to_plus, the cross-sector map from negative four-velocity/covector to the positive optical frame",
        "prove M_minus_to_plus is induced by the same admissible L_minus_to_plus used in the tetrad target",
        "state which metric lowers the negative-sector four-velocity before contraction",
        "keep Q_det separate from Q_cross so density-volume and optical-projection factors are not double counted",
        "derive source-backed negative-sector velocity field before using PM beta fields as physics",
        "state whether the source is dust or perfect fluid, and keep pressure terms explicit when p_s is not negligible",
        "prove compatibility with Bianchi mixed-stress residuals before tensor-lensing claims",
    ]
    return {
        "description": "Covariant target for the Janus Q_cross optical projection factor.",
        "source_anchors": [
            "M15 Eqs. 4a-4b: positive-sector optical source receives cross-sector stress.",
            "M30 Sect. 12-14: exact mixed tensor closure remains open.",
        ],
        "target": target,
        "reductions": reductions,
        "missing_maps": missing_maps,
        "physics_closed": False,
        "verdict": (
            "Q_cross is now reduced to an invariant contraction target. The local "
            "velocity formula is only a frame reduction; the cross-sector map "
            "M_minus_to_plus is still missing."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Q_cross Covariant Projection Target",
        "",
        payload["description"],
        "",
        f"Physics closed: {payload['physics_closed']}",
        "",
        "## Source Anchors",
        "",
    ]
    lines.extend(f"- {item}" for item in payload["source_anchors"])
    lines.extend(["", "## Target", ""])
    for key, value in payload["target"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(
        [
            "",
            "## Reductions",
            "",
            "| case | condition | result | status |",
            "|---|---|---|---|",
        ]
    )
    for row in payload["reductions"]:
        lines.append(
            f"| {row['case']} | {row['condition']} | `{row['result']}` | {row['status']} |"
        )
    lines.extend(["", "## Missing Maps", ""])
    lines.extend(f"- {item}" for item in payload["missing_maps"])
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    return "\n".join(lines)


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(render_markdown(payload), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
