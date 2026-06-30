from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_scouple_accepted_action_search.md")
JSON_PATH = Path("outputs/reports/p0_scouple_accepted_action_search.json")


def build_payload() -> dict:
    source_rows = [
        {
            "source": "M15",
            "action_or_principle": (
                "integral of R_plus sqrt(-g_plus)+R_minus sqrt(-g_minus) "
                "-2 chi L_plus sqrt(-g_plus)-2 chi L_minus sqrt(-g_minus)"
            ),
            "accepted_for": "published Lagrangian derivation of Janus coupled field equations",
            "passes": [
                "derives determinant-weighted cross-source field equations under Janus bivariation",
                "keeps pressure in the diagonal perfect-fluid stress form used by the paper",
            ],
            "fails_for_scouple": [
                "no independent S_couple functional is supplied",
                "no delta S_couple/delta L equation exists",
                "no Q_cross optical transport map is varied",
                "no split Noether proof gives both R_plus=0 and R_minus=0",
                "no anisotropic-stress Pi transport is derived",
            ],
            "accepted_as_scouple": False,
        },
        {
            "source": "M30",
            "action_or_principle": "modern bimetric field-equation and geodesic presentation",
            "accepted_for": "Janus bimetric/geodesic source anchor and Newtonian interaction laws",
            "passes": [
                "anchors two metric/geodesic families",
                "anchors weak-field interaction signs",
            ],
            "fails_for_scouple": [
                "does not provide an independent S_couple action",
                "does not provide pressure/Pi variational closure",
            ],
            "accepted_as_scouple": False,
        },
    ]
    required_acceptance = [
        "source must supply S_couple or explicitly promote it as a new Janus axiom",
        "metric variations must derive K_plus and K_minus",
        "variation with respect to L or the map must derive the same L used by Q_cross",
        "Noether identities must split into both sector residual closures",
        "perfect-fluid pressure and anisotropic stress Pi must be transported as tensors",
        "no observational fit constants or scalar Q_det/Q_cross absorption",
    ]
    return {
        "description": "Search result for an accepted Janus S_couple action that could close split Noether and pressure/Pi.",
        "status": "accepted-scouple-not-found",
        "source_rows": source_rows,
        "required_acceptance": required_acceptance,
        "closest_published_action": "M15 bivariational total action",
        "m15_action_accepted_for_field_equations": True,
        "m15_action_accepted_as_scouple": False,
        "independent_scouple_found": False,
        "delta_scouple_delta_l_found": False,
        "split_noether_closure_found": False,
        "pressure_pi_variational_closure_found": False,
        "can_use_m15_as_scouple_without_new_axiom": False,
        "requires_new_action_axiom_or_source": True,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The accepted Janus action found in M15 derives the coupled field equations "
            "through a constrained bivariation, not through an independent S_couple. "
            "It cannot by itself derive L/Q_cross transport, split Noether closure, or "
            "anisotropic-stress Pi transport."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 S_couple Accepted Action Search",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Closest published action: {payload['closest_published_action']}",
        f"M15 action accepted for field equations: {payload['m15_action_accepted_for_field_equations']}",
        f"M15 action accepted as S_couple: {payload['m15_action_accepted_as_scouple']}",
        f"Independent S_couple found: {payload['independent_scouple_found']}",
        f"delta S_couple / delta L found: {payload['delta_scouple_delta_l_found']}",
        f"Split Noether closure found: {payload['split_noether_closure_found']}",
        f"Pressure/Pi variational closure found: {payload['pressure_pi_variational_closure_found']}",
        f"Can use M15 as S_couple without new axiom: {payload['can_use_m15_as_scouple_without_new_axiom']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Source Rows",
        "",
    ]
    for row in payload["source_rows"]:
        lines.append(f"- {row['source']}: {row['action_or_principle']}")
        lines.append(f"  - accepted for: {row['accepted_for']}")
        lines.append(f"  - accepted as S_couple: {row['accepted_as_scouple']}")
        lines.extend(f"  - pass: {item}" for item in row["passes"])
        lines.extend(f"  - fail: {item}" for item in row["fails_for_scouple"])
    lines.extend(["", "## Required Acceptance", ""])
    lines.extend(f"- {item}" for item in payload["required_acceptance"])
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
