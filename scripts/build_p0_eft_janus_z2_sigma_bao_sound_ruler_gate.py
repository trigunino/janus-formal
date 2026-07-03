from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_bao_sound_ruler_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_bao_sound_ruler_gate.json")


def build_payload() -> dict:
    lock = {
        "background_equations_derived": True,
        "photon_distance_map_derived": True,
        "photon_baryon_sound_speed_declared": True,
        "drag_epoch_condition_declared": True,
        "rd_integral_over_h_z2sigma_declared": True,
        "fitted_planck_rd_forbidden": True,
        "compressed_lcdm_prior_forbidden": True,
    }
    evaluation = {
        "H_Z2Sigma_numerical_ready": False,
        "photon_baryon_sound_speed_ready": False,
        "drag_epoch_ready": False,
        "rd_integral_evaluated": False,
    }
    return {
        "status": "janus-z2-sigma-bao-sound-ruler-gate",
        "active_core": "Z2_tunnel_Sigma",
        "lock": lock,
        "evaluation": evaluation,
        "bao_sound_ruler_lock_closed": all(lock.values()),
        "bao_sound_ruler_formula_ready": all(lock.values()),
        "bao_sound_ruler_evaluated": all(lock.values()) and all(evaluation.values()),
        "rd_definition": "r_d^Z2Sigma = integral_{z_d}^{infinity} c_s^Z2Sigma(z) / H_Z2Sigma(z) dz",
        "distance_ratios_ready": False,
        "fitted_planck_rd_forbidden": True,
        "compressed_lcdm_prior_forbidden": True,
        "non_compressed_bao_gate_ready": False,
        "next_required": [
            "supply_H_Z2Sigma_from_numerical_background_closure",
            "derive_c_s_Z2Sigma_from_active_photon_baryon_plasma",
            "derive_drag_epoch_z_d_Z2Sigma",
            "evaluate_r_d_integral_without_compressed_LCDM_prior",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma BAO Sound Ruler Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"BAO sound ruler formula ready: `{payload['bao_sound_ruler_formula_ready']}`",
        f"BAO sound ruler evaluated: `{payload['bao_sound_ruler_evaluated']}`",
        f"Definition: `{payload['rd_definition']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
