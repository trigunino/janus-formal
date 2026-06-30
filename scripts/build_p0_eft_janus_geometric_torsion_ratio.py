from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_janus_geometric_torsion_ratio.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_geometric_torsion_ratio.json")


def build_payload() -> dict:
    filters = [
        {
            "id": "G1",
            "name": "orbifold-even projection",
            "effect": "odd axial contributions cancel between sheets; q_A enters only through q_A^2 or paired sectors",
            "fixes_ratio": False,
        },
        {
            "id": "G2",
            "name": "radion as solder-volume trace",
            "effect": "trace torsion q_T is tied to derivative of log volume/solder factor",
            "fixes_ratio": "normalizes q_T up to field convention",
        },
        {
            "id": "G3",
            "name": "time-orientation Cartan leg",
            "effect": "axial torsion q_A is allowed only if Janus orientation flip is represented as spin/chirality holonomy",
            "fixes_ratio": False,
        },
        {
            "id": "G4",
            "name": "no parity-odd residue",
            "effect": "forbids unpaired q_A terms in the effective action",
            "fixes_ratio": False,
        },
        {
            "id": "G5",
            "name": "canonical radion normalization",
            "effect": "sets the trace-torsion normalization convention after chi is canonical",
            "fixes_ratio": "q_T = 1 in canonical units",
        },
    ]
    candidate_ratios = [
        {
            "id": "R_trace_only",
            "condition": "q_A = 0, q_T = 1",
            "geometric_status": "cleanest Janus-volume option",
            "risk": "may fail to generate the double-dual/Horndeski structure alone",
        },
        {
            "id": "R_paired_axial_trace",
            "condition": "q_T = 1, q_A^2 fixed by spin holonomy if a Janus PT/chirality law is supplied",
            "geometric_status": "best nontrivial option",
            "risk": "requires an extra Janus spin-holonomy law",
        },
        {
            "id": "R_free_eft",
            "condition": "q_T = 1, q_A remains EFT threshold parameter",
            "geometric_status": "not fully Janus-derived",
            "risk": "becomes parameterized EFT, not zero-rustine geometry",
        },
    ]
    theorem_status = {
        "janus_geometric_filter_written": True,
        "q_T_canonical_trace_fixed": True,
        "q_A_fixed_by_geometry": False,
        "requires_spin_holonomy_law_for_q_A": True,
        "prediction_ready": False,
    }
    return {
        "description": "Janus-geometric attempt to select the torsion/radion heat-kernel ratios q_A/q_T.",
        "status": "trace-fixed-axial-open",
        "theorem_status": theorem_status,
        "filters": filters,
        "candidate_ratios": candidate_ratios,
        "recommended_next_test": "Start with R_trace_only; if it fails to generate double-dual, introduce R_paired_axial_trace and derive/check a spin-holonomy law.",
        "verdict": (
            "Janus geometry can fix q_T by volume/solder normalization. It does not yet fix q_A "
            "unless the model includes a PT/chirality spin-holonomy rule."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Janus Geometric Torsion Ratio",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
    ]
    lines.extend(f"{key}: {value}" for key, value in payload["theorem_status"].items())
    lines.extend(["", "## Filters"])
    for row in payload["filters"]:
        lines.append(f"- {row['id']}: {row['name']} -> {row['effect']}")
    lines.extend(["", "## Candidate Ratios"])
    for row in payload["candidate_ratios"]:
        lines.append(f"- {row['id']}: {row['condition']} ({row['geometric_status']})")
    lines.extend(["", f"Recommended next test: {payload['recommended_next_test']}"])
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
