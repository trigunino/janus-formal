from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_flat_omega_connection_branch.md")
JSON_PATH = Path("outputs/reports/p0_flat_omega_connection_branch.json")


def build_payload() -> dict:
    flatness_conditions = [
        "D_alpha L = Omega_alpha L",
        "Omega_{alpha AB}=-Omega_{alpha BA}",
        "R_Omega_{alpha beta}=D_alpha Omega_beta-D_beta Omega_alpha+[Omega_alpha,Omega_beta]=0",
        "L(x)=P exp integral Omega times L0 becomes path-independent on simply connected domains",
    ]
    what_it_solves = [
        "removes path ambiguity for boundary/initial L propagation",
        "keeps Lorentz admissibility along transport",
        "makes the same L usable for K transport and Q_cross without path choice",
    ]
    what_it_does_not_solve = [
        "does not determine Omega from the zero-divergence PDE",
        "does not prove flatness from Janus action/source equations",
        "does not fix L0 unless source/symmetry boundary is supplied",
        "does not close pressure/Pi or observable normalization",
    ]
    possible_source_routes = [
        "derive flatness from a pure-gauge identification of local tetrad frames",
        "derive non-flat curvature from relative sector curvature and then include holonomy as physical",
        "restrict flatness to FLRW/comoving or weak-perturbation branch only",
    ]
    return {
        "description": "P0 flat Omega-connection branch for path-independent L transport.",
        "status": "flat-connection-branch-open",
        "flatness_condition_written": True,
        "path_independence_if_flat": True,
        "source_derived_flatness": False,
        "unique_l_found": False,
        "physics_closed": False,
        "prediction_ready": False,
        "flatness_conditions": flatness_conditions,
        "what_it_solves": what_it_solves,
        "what_it_does_not_solve": what_it_does_not_solve,
        "possible_source_routes": possible_source_routes,
        "verdict": (
            "Flat Omega is a strong outside-the-box simplifier: it turns L transport "
            "into path-independent parallel transport from L0. It is useful as a "
            "test branch, but must be source-derived or restricted before physics claims."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Flat Omega Connection Branch",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Flatness condition written: {payload['flatness_condition_written']}",
        f"Path independence if flat: {payload['path_independence_if_flat']}",
        f"Source-derived flatness: {payload['source_derived_flatness']}",
        f"Unique L found: {payload['unique_l_found']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Flatness Conditions",
        "",
    ]
    lines.extend(f"- `{item}`" for item in payload["flatness_conditions"])
    lines.extend(["", "## What It Solves", ""])
    lines.extend(f"- {item}" for item in payload["what_it_solves"])
    lines.extend(["", "## What It Does Not Solve", ""])
    lines.extend(f"- {item}" for item in payload["what_it_does_not_solve"])
    lines.extend(["", "## Possible Source Routes", ""])
    lines.extend(f"- {item}" for item in payload["possible_source_routes"])
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
