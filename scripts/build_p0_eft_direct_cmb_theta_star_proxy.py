from __future__ import annotations

from pathlib import Path
import json
import math

try:
    from scripts.build_p0_eft_early_holst_plasma_stress_tensor import build_payload as stress_payload
    from scripts.build_p0_eft_janus_holst_distance_ruler_map import (
        distance_row,
        master_branch_background,
    )
except ModuleNotFoundError:
    from build_p0_eft_early_holst_plasma_stress_tensor import build_payload as stress_payload
    from build_p0_eft_janus_holst_distance_ruler_map import distance_row, master_branch_background


REPORT_PATH = Path("outputs/reports/p0_eft_direct_cmb_theta_star_proxy.md")
JSON_PATH = Path("outputs/reports/p0_eft_direct_cmb_theta_star_proxy.json")


def build_payload() -> dict:
    z_star = 1089.0
    constants, radion = master_branch_background()
    screened_constants = {**constants, "spin_coeff": 0.0}
    distance = distance_row(z_star, screened_constants, radion, samples=2048)
    stress = stress_payload()
    rd_ratio = 1.0 / math.sqrt(1.0 + 0.2271 * stress["derived_delta_Neff"] / (1.0 + 0.2271 * 3.046))
    theta_proxy = rd_ratio / distance["D_M_unit"]
    return {
        "description": "Direct CMB theta_* proxy using Janus-Holst distances and the derived Holst plasma ruler.",
        "status": "direct-cmb-theta-star-proxy-computed-transfer-open",
        "z_star_reference": z_star,
        "uses_lcdm_compressed_planck_parameters_as_verdict": False,
        "spin_background_screened_for_photon_distance": True,
        "D_M_unit_to_recombination": distance["D_M_unit"],
        "D_A_unit_to_recombination": distance["D_M_unit"] / (1.0 + z_star),
        "Delta_Neff_Holst": stress["derived_delta_Neff"],
        "sound_ruler_ratio": rd_ratio,
        "theta_star_proxy_unit": theta_proxy,
        "janus_distance_ruler_proxy_ready": True,
        "cmb_transfer_functions_ready": False,
        "direct_cmb_likelihood_ready": False,
        "is_planck_verdict": False,
        "next_required": "derive uncompressed Janus-Holst transfer functions before comparing to Planck spectra.",
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Direct CMB Theta Star Proxy",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Uses LCDM compressed Planck parameters as verdict: {payload['uses_lcdm_compressed_planck_parameters_as_verdict']}",
        f"Direct CMB likelihood ready: {payload['direct_cmb_likelihood_ready']}",
        "",
        "## Proxy",
        "",
        f"- z_star reference: {payload['z_star_reference']:.6g}",
        f"- D_M unit to recombination: {payload['D_M_unit_to_recombination']:.6g}",
        f"- D_A unit to recombination: {payload['D_A_unit_to_recombination']:.6g}",
        f"- Delta N_eff Holst: {payload['Delta_Neff_Holst']:.6g}",
        f"- sound ruler ratio: {payload['sound_ruler_ratio']:.6g}",
        f"- theta_star proxy unit: {payload['theta_star_proxy_unit']:.6g}",
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
