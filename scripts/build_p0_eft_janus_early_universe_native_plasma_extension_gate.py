from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.janus_early_universe_native_plasma import (
    native_plasma_extension_contract,
)
from scripts.build_p0_eft_janus_projected_photon_baryon_plasma_frontier_gate import (
    build_payload as build_projected_plasma_frontier_payload,
)


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_early_universe_native_plasma_extension_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_early_universe_native_plasma_extension_gate.json"
)


def build_payload() -> dict:
    contract = native_plasma_extension_contract()
    frontier = build_projected_plasma_frontier_payload()
    closed = contract["closed_by_eq40"]
    extension_structured = all(
        [
            closed["fine_structure_invariant"],
            closed["rest_energy_invariant"],
            closed["ionization_energy_invariant"],
            closed["thomson_area_scales_as_a2"],
            closed["compton_length_scales_as_a"],
        ]
    )
    return {
        "status": "janus-early-universe-native-plasma-extension-gate",
        "extension_structured": extension_structured,
        "eq40_microphysics_partially_closed": extension_structured,
        "native_rd_evaluated": frontier["native_rd_evaluated"],
        "native_bao_prediction_ready": frontier["native_bao_prediction_ready"],
        "contract": contract,
        "projected_plasma_frontier": {
            "status": frontier["status"],
            "current_bottom_reached": frontier["current_bottom_reached"],
            "missing_active_inputs": frontier["missing_active_inputs"],
            "hard_blockers": frontier["hard_blockers"],
        },
        "new_extension_result": (
            "Eq40 closes several local microphysics scalings, but it still does "
            "not derive baryon/photon normalizations or pre-drag H_J."
        ),
        "next_required_for_real_closure": [
            "derive N_b^J or rho_b0^J from bimetric/Z2 state",
            "derive photon temperature or occupation law in the variable-constants regime",
            "derive or reject phase-space compensated thermal cooling with occupation exponent +3",
            "derive pre-drag H_J(a) from the two-sector bimetric background",
            "derive redshift map valid to z_d^J",
        ],
        "gate_passed": extension_structured,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    contract = payload["contract"]
    lines = [
        "# Janus Early-Universe Native Plasma Extension",
        "",
        f"Extension structured: `{payload['extension_structured']}`",
        f"Eq40 microphysics partially closed: `{payload['eq40_microphysics_partially_closed']}`",
        f"Native r_d evaluated: `{payload['native_rd_evaluated']}`",
        f"Native BAO prediction ready: `{payload['native_bao_prediction_ready']}`",
        "",
        "## Eq40 closed scalings",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in contract["closed_by_eq40"].items())
    lines.extend(["", "## Scaling exponents"])
    lines.extend(
        f"- `{key}`: `{value}`" for key, value in contract["scaling_exponents"].items()
    )
    lines.extend(["", "## Candidate plasma scaling laws"])
    for candidate in contract["candidate_plasma_scaling_laws"]:
        lines.extend(
            [
                f"### {candidate['name']}",
                f"- rho_gamma exponent: `{candidate['rho_gamma_exponent']}`",
                f"- rho_baryon energy exponent: `{candidate['rho_baryon_energy_exponent']}`",
                f"- baryon loading exponent: `{candidate['baryon_loading_exponent']}`",
                f"- Gamma/H exponent before ionization: `{candidate['Gamma_drag_over_H_exponent_before_ionization']}`",
                f"- temperature energy exponent: `{candidate['temperature_energy_exponent']}`",
                f"- phase-space occupation exponent: `{candidate['phase_space_occupation_exponent']}`",
                f"- blackbody n_gamma exponent: `{candidate['blackbody_photon_number_density_exponent']}`",
                f"- blackbody matches conserved photons: `{candidate['blackbody_matches_conserved_photon_number']}`",
                f"- verdict: `{candidate['verdict']}`",
                "",
            ]
        )
    lines.extend(["", "## Native plasma equations"])
    lines.extend(f"- `{item}`" for item in contract["native_plasma_equations"])
    lines.extend(["", "## Still required"])
    lines.extend(f"- `{item}`" for item in payload["next_required_for_real_closure"])
    lines.extend(["", "## Interpretation", "", contract["interpretation"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
