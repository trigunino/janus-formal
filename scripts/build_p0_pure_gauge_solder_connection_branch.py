from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_pure_gauge_solder_connection_branch.md")
JSON_PATH = Path("outputs/reports/p0_pure_gauge_solder_connection_branch.json")


def build_payload() -> dict:
    construction = [
        "raw solder map L_geom=e_plus E_minus",
        "polar/project to Lorentz part L=polar_eta(L_geom) where defined",
        "define Omega=(D L)L^{-1}",
        "if L is globally defined and smooth, Omega is pure gauge and R_Omega=0",
    ]
    advantages = [
        "source geometry supplies L candidate from the two tetrads",
        "flatness follows mathematically if L is taken as a global Lorentz gauge field",
        "path-independent L can be initialized by FLRW aligned branch",
    ]
    blockers = [
        "L_geom is not Lorentz unless compatibility is proved or polar-projected",
        "polar projection branch may be singular or non-smooth",
        "pure-gauge Omega may erase physical relative curvature/holonomy",
        "not yet shown to solve zero-divergence PDE for K",
    ]
    return {
        "description": "P0 pure-gauge solder connection branch for constructing L/Omega from tetrads.",
        "status": "pure-gauge-branch-open",
        "construction_written": True,
        "flat_if_global_lorentz_l": True,
        "source_derived_lorentz_projection": False,
        "zero_divergence_verified": False,
        "physics_closed": False,
        "prediction_ready": False,
        "construction": construction,
        "advantages": advantages,
        "blockers": blockers,
        "verdict": (
            "Pure gauge is the cleanest path-independent L construction, but it is "
            "only physical if the Lorentz projection is regular and the resulting K "
            "satisfies the zero-divergence PDE."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Pure-Gauge Solder Connection Branch",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Flat if global Lorentz L: {payload['flat_if_global_lorentz_l']}",
        f"Source-derived Lorentz projection: {payload['source_derived_lorentz_projection']}",
        f"Zero-divergence verified: {payload['zero_divergence_verified']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Construction",
        "",
    ]
    lines.extend(f"- `{item}`" for item in payload["construction"])
    lines.extend(["", "## Advantages", ""])
    lines.extend(f"- {item}" for item in payload["advantages"])
    lines.extend(["", "## Blockers", ""])
    lines.extend(f"- {item}" for item in payload["blockers"])
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
