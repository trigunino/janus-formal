from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_l_boundary_initial_condition_branch.md")
JSON_PATH = Path("outputs/reports/p0_l_boundary_initial_condition_branch.json")


def build_payload() -> dict:
    branch_conditions = [
        {
            "condition": "initial Lorentz map",
            "statement": "L_minus_to_plus(x0)=L0 with L0^T eta L0=eta",
            "role": "fixes integration constants for D L = Omega L",
        },
        {
            "condition": "mirror initial map",
            "statement": "L_plus_to_minus(x0)=L0^{-1}",
            "role": "keeps plus/minus transport reciprocal",
        },
        {
            "condition": "source or symmetry boundary",
            "statement": "L0=I in aligned FLRW/comoving limit or specified by a symmetry/source surface",
            "role": "prevents survey-tuned orientation choice",
        },
        {
            "condition": "path/integrability control",
            "statement": "curvature of Omega connection must be specified or vanish on chosen transport family",
            "role": "prevents path-dependent ambiguous L",
        },
    ]
    uniqueness_requirements = [
        "Omega field determined by zero-divergence PDE plus gauge condition",
        "initial/boundary L fixed from source symmetry, not observations",
        "integrability/path rule fixed for transporting L away from the initial surface",
        "same transported L used for K and Q_cross",
    ]
    failure_modes = [
        "arbitrary L0 becomes a fitted lensing normalization",
        "path-dependent L gives non-unique Q_cross",
        "boundary condition closes dust but not pressure/Pi",
        "initial aligned FLRW condition does not by itself fix non-comoving perturbations",
    ]
    return {
        "description": "P0 branch for using initial/boundary conditions on L to lift transverse gauge freedom.",
        "status": "boundary-initial-branch-open",
        "branch_written": True,
        "can_fix_integration_constants": True,
        "source_boundary_found": False,
        "integrability_proved": False,
        "unique_l_found": False,
        "physics_closed": False,
        "prediction_ready": False,
        "branch_conditions": branch_conditions,
        "uniqueness_requirements": uniqueness_requirements,
        "failure_modes": failure_modes,
        "verdict": (
            "Initial/boundary data can help select L only if it is source- or "
            "symmetry-derived and paired with an integrable Omega transport rule. "
            "It cannot be chosen from lensing fits."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 L Boundary/Initial Condition Branch",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Can fix integration constants: {payload['can_fix_integration_constants']}",
        f"Source boundary found: {payload['source_boundary_found']}",
        f"Integrability proved: {payload['integrability_proved']}",
        f"Unique L found: {payload['unique_l_found']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Branch Conditions",
        "",
    ]
    for row in payload["branch_conditions"]:
        lines.append(f"- {row['condition']}: `{row['statement']}`")
        lines.append(f"  - role: {row['role']}")
    lines.extend(["", "## Uniqueness Requirements", ""])
    lines.extend(f"- {item}" for item in payload["uniqueness_requirements"])
    lines.extend(["", "## Failure Modes", ""])
    lines.extend(f"- {item}" for item in payload["failure_modes"])
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
