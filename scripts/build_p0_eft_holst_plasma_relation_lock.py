from __future__ import annotations

from pathlib import Path
import json

try:
    from scripts.build_p0_eft_delta_neff_denominator_bao_score import build_payload as denominator_payload
    from scripts.build_p0_eft_janus_holst_distance_ruler_map import master_branch_background
except ModuleNotFoundError:
    from build_p0_eft_delta_neff_denominator_bao_score import build_payload as denominator_payload
    from build_p0_eft_janus_holst_distance_ruler_map import master_branch_background


REPORT_PATH = Path("outputs/reports/p0_eft_holst_plasma_relation_lock.md")
JSON_PATH = Path("outputs/reports/p0_eft_holst_plasma_relation_lock.json")


def build_payload() -> dict:
    denominator = denominator_payload()
    constants, _ = master_branch_background()
    relation_delta_neff = abs(float(constants["eta_holst"])) * float(constants["Omega_m0"])
    relation_row = next(row for row in denominator["rows"] if row["name"] == "base_eta_omega_m")
    exact_row = next(row for row in denominator["rows"] if row["name"] == "exact_required")
    return {
        "description": "Robust Holst plasma relation lock for the BAO sound-horizon excess.",
        "status": "holst-plasma-relation-lock-scored",
        "relation": "Delta_Neff_Holst = |eta_H| * Omega_m0",
        "eta_H_abs": abs(float(constants["eta_holst"])),
        "Omega_m0": float(constants["Omega_m0"]),
        "relation_delta_Neff": relation_delta_neff,
        "relation_dv_factor": relation_row["dv_factor"],
        "relation_chi2": relation_row["chi2"],
        "relation_reduced_chi2": relation_row["reduced_chi2"],
        "exact_required_chi2": exact_row["chi2"],
        "chi2_penalty_vs_exact": relation_row["chi2"] - exact_row["chi2"],
        "passes_bao_shape_gate": relation_row["chi2"] < 30.0,
        "micro_residual_is_phenomenologically_critical": abs(relation_row["chi2"] - exact_row["chi2"]) > 1.0,
        "is_derived_geometry": False,
        "next_required": "derive Delta_Neff_Holst = |eta_H| * Omega_m0 from the early Holst plasma stress tensor.",
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Holst Plasma Relation Lock",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Derived geometry: {payload['is_derived_geometry']}",
        f"Passes BAO shape gate: {payload['passes_bao_shape_gate']}",
        "",
        "## Relation",
        "",
        f"- relation: `{payload['relation']}`",
        f"- |eta_H|: {payload['eta_H_abs']:.6g}",
        f"- Omega_m0: {payload['Omega_m0']:.6g}",
        f"- Delta N_eff: {payload['relation_delta_Neff']:.6g}",
        f"- D_V factor: {payload['relation_dv_factor']:.6g}",
        f"- chi2: {payload['relation_chi2']:.6g}",
        f"- chi2 penalty vs exact: {payload['chi2_penalty_vs_exact']:.6g}",
        f"- micro residual critical: {payload['micro_residual_is_phenomenologically_critical']}",
        "",
        "## Next",
        "",
        payload["next_required"],
        "",
    ]
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
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
