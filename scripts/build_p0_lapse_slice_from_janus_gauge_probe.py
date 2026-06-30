from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_lapse_slice_from_janus_gauge_probe.md")
JSON_PATH = Path("outputs/reports/p0_lapse_slice_from_janus_gauge_probe.json")


def build_payload() -> dict:
    n_s, n_r, sg_s, sg_r, j_phi, b4 = sp.symbols("N_s N_r sqrt_gamma_s sqrt_gamma_r J_phi B4", positive=True)
    b_identity = sp.Eq(b4, j_phi * n_s * sg_s / (n_r * sg_r))
    lapse_ratio = sp.solve(b_identity, n_s / n_r)[0]
    j_solution = sp.solve(b_identity, j_phi)[0]
    comoving_unit_lapse_solution = sp.solve([sp.Eq(n_s, 1), sp.Eq(n_r, 1)], [n_s, n_r], dict=True)
    rows = [
        {
            "condition": "proper_time_comoving_both_sectors",
            "derives": "N_s=N_r=1 only after choosing each sector's comoving proper-time slicing",
            "fixes_lapse_ratio": True,
            "source_equation_only": False,
        },
        {
            "condition": "m15_b4vol_source_weight",
            "derives": f"N_s/N_r={lapse_ratio}",
            "fixes_lapse_ratio": False,
            "source_equation_only": True,
        },
        {
            "condition": "spatial_slice_ratio_supplied",
            "derives": f"J_phi={j_solution}",
            "fixes_j_phi": True,
            "source_equation_only": False,
        },
        {
            "condition": "flrw_comoving_shared_time",
            "derives": "special branch can set lapse ratio and slice ratio from the FLRW ansatz",
            "fixes_lapse_ratio": True,
            "source_equation_only": False,
        },
    ]
    return {
        "description": "Probe for deriving lapse/slice gauge conditions needed to select J_phi from Janus B4vol.",
        "status": "lapse-slice-gauge-derivation-conditional",
        "b4vol_identity": "B4=J_phi*N_s*sqrt_gamma_s/(N_r*sqrt_gamma_r)",
        "lapse_ratio_from_b4vol": str(lapse_ratio),
        "j_phi_from_b4vol": str(j_solution),
        "comoving_unit_lapse_solution": str(comoving_unit_lapse_solution),
        "rows": rows,
        "janus_field_equations_fix_lapse_slice": False,
        "proper_time_slicing_can_fix_lapse": True,
        "flrw_comoving_branch_can_fix_lapse_slice": True,
        "general_perturbed_branch_lapse_slice_fixed": False,
        "j_phi_selected_without_slice_data": False,
        "new_gauge_axiom_risk": True,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "Proper-time/comoving slicing can fix lapse in restricted branches, and FLRW can "
            "fix lapse/slice by ansatz. The general perturbed Janus equations still fix only "
            "B4vol, not J_phi alone, without an additional slicing/gauge law."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Lapse/Slice From Janus Gauge Probe",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"B4vol identity: `{payload['b4vol_identity']}`",
        f"Lapse ratio from B4vol: `{payload['lapse_ratio_from_b4vol']}`",
        f"J_phi from B4vol: `{payload['j_phi_from_b4vol']}`",
        f"Comoving unit lapse solution: `{payload['comoving_unit_lapse_solution']}`",
        f"Janus field equations fix lapse/slice: {payload['janus_field_equations_fix_lapse_slice']}",
        f"Proper-time slicing can fix lapse: {payload['proper_time_slicing_can_fix_lapse']}",
        f"FLRW comoving branch can fix lapse/slice: {payload['flrw_comoving_branch_can_fix_lapse_slice']}",
        f"General perturbed branch lapse/slice fixed: {payload['general_perturbed_branch_lapse_slice_fixed']}",
        f"J_phi selected without slice data: {payload['j_phi_selected_without_slice_data']}",
        f"New gauge axiom risk: {payload['new_gauge_axiom_risk']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Rows",
        "",
        "| condition | derives | fixes lapse ratio | source equation only |",
        "|---|---|---:|---:|",
    ]
    for row in payload["rows"]:
        lines.append(
            f"| {row['condition']} | `{row['derives']}` | "
            f"{row.get('fixes_lapse_ratio', row.get('fixes_j_phi', False))} | "
            f"{row['source_equation_only']} |"
        )
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
