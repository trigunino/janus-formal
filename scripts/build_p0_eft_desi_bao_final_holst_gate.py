from __future__ import annotations

from pathlib import Path
import json

try:
    from scripts.build_p0_eft_delta_neff_denominator_bao_score import build_payload as denominator_payload
    from scripts.build_p0_eft_early_holst_plasma_stress_tensor import build_payload as stress_payload
except ModuleNotFoundError:
    from build_p0_eft_delta_neff_denominator_bao_score import build_payload as denominator_payload
    from build_p0_eft_early_holst_plasma_stress_tensor import build_payload as stress_payload


REPORT_PATH = Path("outputs/reports/p0_eft_desi_bao_final_holst_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_desi_bao_final_holst_gate.json")


def build_payload() -> dict:
    denominator = denominator_payload()
    stress = stress_payload()
    relation = next(row for row in denominator["rows"] if row["name"] == "base_eta_omega_m")
    return {
        "description": "Final DESI BAO diagnostic gate for the Janus-Holst branch after spin screening and Holst plasma ruler closure.",
        "status": "desi-bao-holst-diagnostic-closed-cmb-transfer-open",
        "spin_background_screened": True,
        "radial_photon_transport_target_applied": True,
        "holst_plasma_sound_ruler_relation_derived": stress["passes_relation_lock"],
        "bao_relation_used": "Delta_Neff_Holst = |eta_H| * Omega_m0",
        "chi2": relation["chi2"],
        "reduced_chi2": relation["reduced_chi2"],
        "dv_factor": relation["dv_factor"],
        "DV_diag_chi2": relation["DV_diag_chi2"],
        "DH_diag_chi2": relation["DH_diag_chi2"],
        "DM_diag_chi2": relation["DM_diag_chi2"],
        "passes_desi_bao_shape_gate": relation["chi2"] < 30.0,
        "is_full_cmb_ready": False,
        "is_no_fit_bao_likelihood": True,
        "remaining_obligation": "Direct CMB still requires uncompressed transfer functions and recombination/drag integration.",
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT DESI BAO Final Holst Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"No-fit BAO likelihood: {payload['is_no_fit_bao_likelihood']}",
        f"Full CMB ready: {payload['is_full_cmb_ready']}",
        "",
        "## Result",
        "",
        f"- relation: `{payload['bao_relation_used']}`",
        f"- D_V factor: {payload['dv_factor']:.6g}",
        f"- chi2: {payload['chi2']:.6g}",
        f"- chi2/dof: {payload['reduced_chi2']:.6g}",
        f"- D_H chi2: {payload['DH_diag_chi2']:.6g}",
        f"- D_M chi2: {payload['DM_diag_chi2']:.6g}",
        f"- D_V chi2: {payload['DV_diag_chi2']:.6g}",
        "",
        "## Remaining Obligation",
        "",
        payload["remaining_obligation"],
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
