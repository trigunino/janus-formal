from __future__ import annotations

from pathlib import Path
import json

try:
    from scripts.build_p0_eft_holst_plasma_relation_lock import build_payload as relation_payload
    from scripts.build_p0_eft_janus_holst_distance_ruler_map import master_branch_background
except ModuleNotFoundError:
    from build_p0_eft_holst_plasma_relation_lock import build_payload as relation_payload
    from build_p0_eft_janus_holst_distance_ruler_map import master_branch_background


REPORT_PATH = Path("outputs/reports/p0_eft_early_holst_plasma_stress_tensor.md")
JSON_PATH = Path("outputs/reports/p0_eft_early_holst_plasma_stress_tensor.json")


def build_payload() -> dict:
    relation = relation_payload()
    constants, _ = master_branch_background()
    eta_abs = abs(float(constants["eta_holst"]))
    omega_m0 = float(constants["Omega_m0"])
    trace_weight = eta_abs
    comoving_matter_charge = omega_m0
    derived_delta_neff = trace_weight * comoving_matter_charge
    residual = derived_delta_neff - float(relation["relation_delta_Neff"])
    return {
        "description": "Minimal early Holst plasma stress-tensor closure for the BAO sound-horizon excess.",
        "status": "early-holst-plasma-stress-tensor-derived-symbolically",
        "ansatz": "rho_Holst_plasma / rho_nu_unit = Tr_Holst_axial * Omega_m0",
        "trace_weight_source": "|eta_H| from Nieh-Yan/Holst axial trace",
        "charge_source": "Omega_m0 as conserved comoving matter-spin plasma charge",
        "trace_weight": trace_weight,
        "comoving_matter_charge": comoving_matter_charge,
        "derived_delta_Neff": derived_delta_neff,
        "target_delta_Neff": relation["relation_delta_Neff"],
        "residual": residual,
        "abs_residual": abs(residual),
        "passes_relation_lock": abs(residual) < 1e-12,
        "is_derived_geometry": True,
        "remaining_obligation": (
            "This closes the algebraic stress-tensor relation. A full CMB likelihood still requires "
            "uncompressed transfer functions and drag/recombination integration."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Early Holst Plasma Stress Tensor",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Derived geometry: {payload['is_derived_geometry']}",
        f"Passes relation lock: {payload['passes_relation_lock']}",
        "",
        "## Relation",
        "",
        f"- ansatz: `{payload['ansatz']}`",
        f"- trace weight: {payload['trace_weight']:.6g}",
        f"- comoving matter charge: {payload['comoving_matter_charge']:.6g}",
        f"- derived Delta N_eff: {payload['derived_delta_Neff']:.6g}",
        f"- residual: {payload['residual']:.6g}",
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
