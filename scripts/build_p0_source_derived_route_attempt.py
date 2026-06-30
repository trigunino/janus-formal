from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_source_derived_route_attempt.md")
JSON_PATH = Path("outputs/reports/p0_source_derived_route_attempt.json")


def build_payload() -> dict:
    source_attempts = [
        {
            "source": "M15",
            "route": "variational determinant-coupled field equations",
            "supplies": [
                "coupled metric variation",
                "B_4vol determinant source factors",
                "two-sector field equations",
            ],
            "missing_for_solution": [
                "Euler-Lagrange variable for cross-tetrad L",
                "Noether identity containing D_alpha L",
                "stress variation proving K_plus/K_minus transport",
            ],
            "usable_condition": "if an interaction action S_int[g_plus,g_minus,L,matter] is added, its diffeomorphism identity must imply R_plus=R_minus=0",
            "closed": False,
        },
        {
            "source": "M30",
            "route": "Bianchi/zero-divergence mixed stress tensor",
            "supplies": [
                "modern bimetric geodesic anchor",
                "mixed stationary coupled equations",
                "zero-divergence requirement for the exact interaction tensor",
            ],
            "missing_for_solution": [
                "explicit exact K_plus/K_minus tensor",
                "source-derived D L transport law",
                "proof beyond Newtonian/TOV asymptotic branches",
            ],
            "usable_condition": "solve for K as a covariant zero-divergence tensor only with boundary/gauge data derived from Janus, not observations",
            "closed": False,
        },
        {
            "source": "M31",
            "route": "symplectic torsor symmetry",
            "supplies": [
                "sector transformation classification",
                "energy/momentum/charge symmetry anchor",
                "candidate group-theoretic constraint on allowed L sectors",
            ],
            "missing_for_solution": [
                "connection on spacetime tetrad bundle",
                "curvature/path rule for Omega",
                "Noether current tied to K_plus/K_minus",
            ],
            "usable_condition": "use torsor symmetry only as an admissibility filter for L; it is not yet a transport equation",
            "closed": False,
        },
    ]
    candidate_solution_shape = [
        "choose a dynamical or constrained L variable only if a source gives it",
        "derive Omega_alpha=(D_alpha L)L^{-1} from action, connection, or symmetry",
        "derive K_plus/K_minus by varying the same source object",
        "derive Q_cross from the same L and same path rule",
        "prove the resulting Noether/Bianchi identity gives R_plus=0 and R_minus=0",
    ]
    return {
        "description": "Direct attempt to extract a source-derived closure route from M15, M30, and M31.",
        "status": "attempt-open-no-source-closure-found",
        "sources_checked": ["M15", "M30", "M31"],
        "source_derived_solution_found": False,
        "physics_closed": False,
        "prediction_ready": False,
        "source_attempts": source_attempts,
        "candidate_solution_shape": candidate_solution_shape,
        "strongest_result": (
            "M30 gives the sharpest target: exact K must be zero-divergence. "
            "M15 anchors determinant source factors. M31 can restrict admissible "
            "sector maps. None currently supplies D L or K explicitly."
        ),
        "next_action": (
            "Try deriving a constrained interaction action with L as auxiliary field, "
            "then test whether its Noether identity reproduces the M30 zero-divergence condition."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Source-Derived Route Attempt",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Sources checked: {', '.join(payload['sources_checked'])}",
        f"Source-derived solution found: {payload['source_derived_solution_found']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| source | route | supplies | missing for solution | usable condition | closed |",
        "|---|---|---|---|---|---|",
    ]
    for row in payload["source_attempts"]:
        lines.append(
            f"| {row['source']} | {row['route']} | {'; '.join(row['supplies'])} | "
            f"{'; '.join(row['missing_for_solution'])} | {row['usable_condition']} | {row['closed']} |"
        )
    lines.extend(["", "## Candidate Solution Shape", ""])
    lines.extend(f"- {item}" for item in payload["candidate_solution_shape"])
    lines.extend(["", f"Strongest result: {payload['strongest_result']}"])
    lines.extend([f"Next action: {payload['next_action']}", ""])
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
