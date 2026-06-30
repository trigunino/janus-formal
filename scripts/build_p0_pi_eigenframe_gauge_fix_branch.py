from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_pi_eigenframe_gauge_fix_branch.md")
JSON_PATH = Path("outputs/reports/p0_pi_eigenframe_gauge_fix_branch.json")


def build_payload() -> dict:
    eigen_cases = [
        {
            "case": "Pi=0",
            "eigenstructure": "no spatial principal axes",
            "rotation_fixed": "none",
            "remaining_gauge": "SO(3) rest-space rotations",
        },
        {
            "case": "Pi has three distinct spatial eigenvalues",
            "eigenstructure": "three principal axes up to signs/permutations",
            "rotation_fixed": "full rest-space orientation, modulo discrete axis choices",
            "remaining_gauge": "no continuous rest-space rotation",
        },
        {
            "case": "Pi has two equal spatial eigenvalues",
            "eigenstructure": "one principal axis plus degenerate 2-plane",
            "rotation_fixed": "axis normal to degenerate plane",
            "remaining_gauge": "SO(2) rotation inside degenerate plane",
        },
    ]
    omega_constraints = [
        "D(Pi_to) = L(D Pi)L^T + Omega Pi_to + Pi_to Omega^T",
        "if Pi evolution is declared in the transported eigenframe, off-diagonal components constrain rest-space Omega rotations",
        "nondegenerate Pi can fix the continuous transverse gauge left by dust",
        "degenerate or zero Pi cannot fix all screen rotations",
    ]
    source_requirements = [
        "source-derived Pi evolution law",
        "physical reason negative/positive sector has nonzero nondegenerate Pi",
        "same L transports rho, p, Pi and defines Q_cross",
        "R_plus/R_minus closure with B_4vol gradients after adding Pi terms",
    ]
    return {
        "description": "P0 Pi eigenframe branch for fixing transverse Lorentz gauge.",
        "status": "pi-eigenframe-branch-open",
        "eigenframe_algebra_written": True,
        "can_fix_full_rotation_if_nondegenerate": True,
        "source_derived_pi_evolution": False,
        "unique_omega_found": False,
        "physics_closed": False,
        "prediction_ready": False,
        "eigen_cases": eigen_cases,
        "omega_constraints": omega_constraints,
        "source_requirements": source_requirements,
        "verdict": (
            "A nondegenerate anisotropic stress tensor can fix the continuous "
            "rest-space orientation left free by dust. This becomes physical only "
            "if Pi and its evolution are source-derived."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Pi Eigenframe Gauge-Fix Branch",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Eigenframe algebra written: {payload['eigenframe_algebra_written']}",
        f"Can fix full rotation if nondegenerate: {payload['can_fix_full_rotation_if_nondegenerate']}",
        f"Source-derived Pi evolution: {payload['source_derived_pi_evolution']}",
        f"Unique Omega found: {payload['unique_omega_found']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Eigen Cases",
        "",
        "| case | eigenstructure | rotation fixed | remaining gauge |",
        "|---|---|---|---|",
    ]
    for row in payload["eigen_cases"]:
        lines.append(
            f"| {row['case']} | {row['eigenstructure']} | {row['rotation_fixed']} | {row['remaining_gauge']} |"
        )
    lines.extend(["", "## Omega Constraints", ""])
    lines.extend(f"- `{item}`" for item in payload["omega_constraints"])
    lines.extend(["", "## Source Requirements", ""])
    lines.extend(f"- {item}" for item in payload["source_requirements"])
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
