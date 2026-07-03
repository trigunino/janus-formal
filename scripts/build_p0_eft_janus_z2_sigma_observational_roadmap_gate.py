from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_observational_roadmap_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_observational_roadmap_gate.json")


def build_payload() -> dict:
    equation_locks = {
        "background_equations_derived": True,
        "sigma_photon_geodesic_map_derived": True,
        "bao_sound_ruler_formula_ready": True,
        "bao_sound_ruler_evaluated": False,
        "growth_perturbation_equations_derived": True,
        "cmb_boltzmann_equations_derived": True,
    }
    return {
        "status": "janus-z2-sigma-observational-roadmap-gate",
        "active_core": "Z2_tunnel_Sigma",
        "z2_sigma_pure_math_closed": True,
        "legacy_z4_archived": True,
        "z4_physics_reactivation_forbidden": True,
        "equation_locks": equation_locks,
        "observation_equation_locks_closed": all(
            value
            for key, value in equation_locks.items()
            if key != "bao_sound_ruler_evaluated"
        ),
        "observation_prediction_inputs_ready": all(equation_locks.values()),
        "non_compressed_observation_gates_passed": False,
        "full_cosmology_prediction_ready_no_fit": False,
        "next_required": [
            "evaluate_z2_sigma_bao_sound_ruler_without_fitted_rd",
            "run_non_compressed_growth_bao_cmb_gates",
        ],
        "forbidden": [
            "reactivate_cyclic_z4_without_monodromy",
            "reuse_archived_z4_cmb_candidate_as_active_evidence",
            "claim_full_no_fit_cosmology",
            "use_planck_lcdm_compressed_parameters_as_validation",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Observational Roadmap Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Pure math closed: `{payload['z2_sigma_pure_math_closed']}`",
        f"Legacy Z4 archived: `{payload['legacy_z4_archived']}`",
        f"Observation equation locks closed: `{payload['observation_equation_locks_closed']}`",
        f"Observation prediction inputs ready: `{payload['observation_prediction_inputs_ready']}`",
        f"Full cosmology no-fit ready: `{payload['full_cosmology_prediction_ready_no_fit']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    lines.extend(["", "## Forbidden"])
    lines.extend(f"- `{item}`" for item in payload["forbidden"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
