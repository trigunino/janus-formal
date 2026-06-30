from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_dl_source_law_traceability_gate.md")
JSON_PATH = Path("outputs/reports/p0_dl_source_law_traceability_gate.json")


def build_payload() -> dict:
    trace_rows = [
        {
            "row": "lorentz_generator",
            "source": "D_alpha L = F_alpha L, F^T eta + eta F=0",
            "source_derived": False,
        },
        {
            "row": "mirror_inverse_transport",
            "source": "D L^{-1} = -L^{-1}(D L)L^{-1}",
            "source_derived": False,
        },
        {
            "row": "transported_continuity_force",
            "source": "F contractions along dust flow",
            "source_derived": False,
        },
        {
            "row": "density_measure_terms",
            "source": "same B/J_phi/Q_det convention",
            "source_derived": False,
        },
        {
            "row": "same_l_k_qcross",
            "source": "one L for K transport and optical Q_cross",
            "source_derived": False,
        },
    ]
    return {
        "description": "Traceability gate for whether the D L source law is derived or only constrained.",
        "status": "dl-source-law-traceability-open",
        "trace_rows": trace_rows,
        "f_equation_constraints_written": True,
        "source_derived_dl_law_found": False,
        "all_trace_rows_source_derived": False,
        "r_plus_closed": False,
        "r_minus_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "F-equation constraints are conditionally sufficient for dust residual closure, "
            "but D L is not a source law until every trace row is source-derived."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 DL Source Law Traceability Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"F-equation constraints written: {payload['f_equation_constraints_written']}",
        f"Source-derived DL law found: {payload['source_derived_dl_law_found']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| row | source | source-derived |",
        "|---|---|---|",
    ]
    for row in payload["trace_rows"]:
        lines.append(f"| {row['row']} | {row['source']} | {row['source_derived']} |")
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
