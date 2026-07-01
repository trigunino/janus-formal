from __future__ import annotations

from pathlib import Path
import json

try:
    from scripts.build_p0_eft_janus_holst_distance_ruler_map import master_branch_background
    from scripts.build_p0_eft_sound_horizon_drag_target import build_payload as sound_target
except ModuleNotFoundError:
    from build_p0_eft_janus_holst_distance_ruler_map import master_branch_background
    from build_p0_eft_sound_horizon_drag_target import build_payload as sound_target


REPORT_PATH = Path("outputs/reports/p0_eft_drag_epoch_e2_excess_carriers.md")
JSON_PATH = Path("outputs/reports/p0_eft_drag_epoch_e2_excess_carriers.json")


def build_payload() -> dict:
    target = sound_target()
    constants, _ = master_branch_background()
    z_drag = 1059.0
    a_drag = 1.0 / (1.0 + z_drag)
    omega_m0 = float(constants["Omega_m0"])
    spin_coeff = float(constants["spin_coeff"])
    omega_r0_reference = 9.2e-5
    e2_reference = omega_m0 * a_drag**-3 + omega_r0_reference * a_drag**-4
    required_delta_e2 = float(target["required_fractional_E2_excess"]) * e2_reference
    spin_a6_unit = spin_coeff * (omega_m0 * a_drag**-3) ** 2
    xi_spin_drag_required = required_delta_e2 / spin_a6_unit
    natural_projection_floor = 1e-6
    standard_neff = 3.046
    neutrino_factor = 0.2271
    delta_neff_radiation_dom = (
        float(target["required_fractional_E2_excess"]) * (1.0 + neutrino_factor * standard_neff) / neutrino_factor
    )
    return {
        "description": "Candidate carriers for the Janus-Holst drag-epoch E^2 excess required by the BAO sound horizon.",
        "status": "drag-epoch-e2-excess-carriers-scored",
        "z_drag_reference": z_drag,
        "a_drag_reference": a_drag,
        "required_fractional_E2_excess": target["required_fractional_E2_excess"],
        "required_delta_E2_reference": required_delta_e2,
        "reference_E2": e2_reference,
        "spin_a6_unit_E2": spin_a6_unit,
        "xi_spin_drag_required": xi_spin_drag_required,
        "delta_Neff_radiation_dominated_equivalent": delta_neff_radiation_dom,
        "natural_projection_floor": natural_projection_floor,
        "spin_a6_as_natural_homogeneous_carrier_viable": xi_spin_drag_required >= natural_projection_floor,
        "preferred_carrier": "radiation_like_holst_plasma_excess",
        "is_derived_geometry": False,
        "next_required": "derive a radiation-like Holst/plasma contribution of Delta E2/E2 ~= 0.094 at drag epoch without reactivating homogeneous a^-6 spin.",
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Drag-Epoch E2 Excess Carriers",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Derived geometry: {payload['is_derived_geometry']}",
        "",
        "## Carrier Diagnostics",
        "",
        f"- z_drag reference: {payload['z_drag_reference']:.6g}",
        f"- required Delta E2 / E2: {payload['required_fractional_E2_excess']:.6g}",
        f"- xi_spin_drag required for homogeneous a^-6 spin: {payload['xi_spin_drag_required']:.6g}",
        f"- natural projection floor: {payload['natural_projection_floor']:.6g}",
        f"- homogeneous a^-6 spin naturally viable: {payload['spin_a6_as_natural_homogeneous_carrier_viable']}",
        f"- radiation-dominated Delta N_eff equivalent: {payload['delta_Neff_radiation_dominated_equivalent']:.6g}",
        f"- preferred carrier: {payload['preferred_carrier']}",
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
