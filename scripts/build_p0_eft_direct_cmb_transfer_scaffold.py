from __future__ import annotations

from pathlib import Path
import json

try:
    from scripts.build_p0_eft_direct_cmb_theta_star_proxy import build_payload as theta_payload
except ModuleNotFoundError:
    from build_p0_eft_direct_cmb_theta_star_proxy import build_payload as theta_payload


REPORT_PATH = Path("outputs/reports/p0_eft_direct_cmb_transfer_scaffold.md")
JSON_PATH = Path("outputs/reports/p0_eft_direct_cmb_transfer_scaffold.json")


def build_payload() -> dict:
    theta = theta_payload()
    state_vector = [
        "Theta0_photon_monopole",
        "Theta1_photon_dipole",
        "delta_b_baryon",
        "v_b_baryon_velocity",
        "delta_m_matter",
        "Phi_newtonian_potential",
        "Psi_curvature_potential",
        "E_Weyl_lensing_source",
    ]
    source_terms = [
        {
            "name": "H_Janus_Holst",
            "status": "available_from_distance_proxy",
            "role": "background clock for transfer ODEs",
        },
        {
            "name": "Delta_Neff_Holst",
            "status": "available_from_early_plasma_stress_tensor",
            "role": "radiation-like early expansion/ruler correction",
        },
        {
            "name": "spin_background_projection",
            "status": "screened_for_homogeneous_photon_distance",
            "role": "prevents a^-6 spin from entering photon background",
        },
        {
            "name": "Weyl_source",
            "status": "open",
            "role": "required for CMB lensing and high-l TT smoothing",
        },
        {
            "name": "visibility_function",
            "status": "open",
            "role": "required for recombination/drag integration",
        },
    ]
    return {
        "description": "Uncompressed Janus-Holst CMB transfer-function scaffold.",
        "status": "direct-cmb-transfer-scaffold-encoded-spectra-open",
        "uses_lcdm_compressed_planck_parameters_as_verdict": False,
        "theta_star_proxy_ready": theta["janus_distance_ruler_proxy_ready"],
        "theta_star_proxy_unit": theta["theta_star_proxy_unit"],
        "state_vector": state_vector,
        "source_terms": source_terms,
        "transfer_equations_encoded": True,
        "background_and_ruler_inputs_ready": True,
        "weyl_lensing_source_ready": False,
        "visibility_function_ready": False,
        "numerical_boltzmann_solver_ready": False,
        "cmb_spectra_ready": False,
        "direct_cmb_likelihood_ready": False,
        "next_required": "derive Weyl source and recombination visibility, then integrate the transfer ODEs into C_ell spectra.",
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Direct CMB Transfer Scaffold",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Uses LCDM compressed Planck verdict: {payload['uses_lcdm_compressed_planck_parameters_as_verdict']}",
        f"Theta proxy ready: {payload['theta_star_proxy_ready']}",
        f"Direct CMB likelihood ready: {payload['direct_cmb_likelihood_ready']}",
        "",
        "## State Vector",
        "",
    ]
    lines.extend(f"- `{item}`" for item in payload["state_vector"])
    lines.extend(["", "## Source Terms", "", "| name | status | role |", "|---|---|---|"])
    for row in payload["source_terms"]:
        lines.append(f"| {row['name']} | {row['status']} | {row['role']} |")
    lines.extend(["", "## Next", "", payload["next_required"], ""])
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
