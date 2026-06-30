from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_branch_decision_matrix.md")
JSON_PATH = Path("outputs/reports/p0_branch_decision_matrix.json")


def build_payload() -> dict:
    branches = [
        {
            "branch": "naive_copied_stress",
            "rank": "reject",
            "closes_dust_force": False,
            "fixes_rotation": False,
            "source_risk": "not tensorially compatible",
            "next_action": "do not pursue",
        },
        {
            "branch": "determinant_weighted_copy",
            "rank": "reject",
            "closes_dust_force": False,
            "fixes_rotation": False,
            "source_risk": "scalar volume factor replaces tensor transport",
            "next_action": "use only as double-counting audit",
        },
        {
            "branch": "lorentz_dust_plus_fermi_walker",
            "rank": "primary",
            "closes_dust_force": "conditionally",
            "fixes_rotation": "along dust flow only",
            "source_risk": "Fermi-Walker must be derived from Janus geometry",
            "next_action": "derive receiver-geodesic and density-measure closure",
        },
        {
            "branch": "perfect_fluid_transport",
            "rank": "secondary",
            "closes_dust_force": "extends to pressure if w_cross source-derived",
            "fixes_rotation": False,
            "source_risk": "isotropic pressure cannot fix screen orientation",
            "next_action": "use after dust if pressure is physically required",
        },
        {
            "branch": "anisotropic_stress_transport",
            "rank": "conditional",
            "closes_dust_force": "extends tensor closure if Pi evolution source-derived",
            "fixes_rotation": "only for nondegenerate Pi",
            "source_risk": "Pi may be absent/degenerate or evolution unspecified",
            "next_action": "use only if source model requires Pi",
        },
        {
            "branch": "bianchi_solved_k_pde",
            "rank": "diagnostic",
            "closes_dust_force": "by construction only after boundary/gauge choice",
            "fixes_rotation": "depends on chosen minimization/gauge",
            "source_risk": "can become an added variational principle",
            "next_action": "use to discover constraints, not as proof",
        },
    ]
    primary_route = [
        "keep Lorentz-dust plus Fermi-Walker as the minimal no-rustine candidate",
        "derive receiver-geodesic transport for u_-to+ and u_+to-",
        "derive B_plus/B_minus density-measure closure",
        "then test R_plus=0 and R_minus=0 before adding pressure/Pi",
    ]
    escalation_rules = [
        "add perfect-fluid only if pressure appears in the source sector under study",
        "add Pi only if anisotropic stress is physically present or required by observations/sources",
        "do not add Pi merely to fix gauge freedom",
        "do not use PDE-solved K as prediction without independent source principle",
    ]
    return {
        "description": "Decision matrix for P0 interaction-tensor branch priority.",
        "status": "decision-matrix-open",
        "primary_branch": "lorentz_dust_plus_fermi_walker",
        "primary_branch_prediction_ready": False,
        "branches": branches,
        "primary_route": primary_route,
        "escalation_rules": escalation_rules,
        "verdict": (
            "The best next path is minimal: Lorentz-transported dust with Fermi-Walker "
            "rotation gauge, then derive receiver-geodesic and density-measure closure. "
            "Perfect-fluid and Pi are escalation branches, not patches."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Branch Decision Matrix",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Primary branch: {payload['primary_branch']}",
        f"Primary branch prediction ready: {payload['primary_branch_prediction_ready']}",
        "",
        "| branch | rank | closes dust force | fixes rotation | source risk | next action |",
        "|---|---|---|---|---|---|",
    ]
    for row in payload["branches"]:
        lines.append(
            f"| {row['branch']} | {row['rank']} | {row['closes_dust_force']} | "
            f"{row['fixes_rotation']} | {row['source_risk']} | {row['next_action']} |"
        )
    lines.extend(["", "## Primary Route", ""])
    lines.extend(f"- {item}" for item in payload["primary_route"])
    lines.extend(["", "## Escalation Rules", ""])
    lines.extend(f"- {item}" for item in payload["escalation_rules"])
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
