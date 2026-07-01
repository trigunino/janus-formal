from __future__ import annotations

from pathlib import Path
import json
import math

try:
    from scripts.build_p0_eft_sound_horizon_global_integral import build_payload as sound_global
except ModuleNotFoundError:
    from build_p0_eft_sound_horizon_global_integral import build_payload as sound_global


REPORT_PATH = Path("outputs/reports/p0_eft_early_deficit_carriers.md")
JSON_PATH = Path("outputs/reports/p0_eft_early_deficit_carriers.json")

NEUTRINO_FACTOR = 0.22710731766


def build_payload() -> dict:
    sound = sound_global()
    neff_ref = float(sound["neff_ref"])
    delta_current = float(sound["delta_neff_janus_holst"])
    delta_required = float(sound["required_delta_neff_for_bao_ratio"])
    delta_missing = float(sound["delta_neff_shortfall"])
    radiation_denominator = 1.0 + NEUTRINO_FACTOR * (neff_ref + delta_current)
    missing_fractional_e2 = NEUTRINO_FACTOR * delta_missing / radiation_denominator
    required_geff_boost = 1.0 + missing_fractional_e2
    vector_same_temp_delta_neff = 8.0 / 7.0
    torsion_vector_temperature_ratio = (delta_missing / vector_same_temp_delta_neff) ** 0.25
    return {
        "description": "Carrier audit for the missing pre-drag sound-horizon energy budget.",
        "status": "early-deficit-carriers-scored",
        "delta_neff_current": delta_current,
        "delta_neff_required": delta_required,
        "delta_neff_missing": delta_missing,
        "missing_fractional_E2_on_current_radiation_branch": missing_fractional_e2,
        "equivalent_pre_drag_Geff_boost": required_geff_boost,
        "equivalent_pre_drag_H_boost": math.sqrt(required_geff_boost),
        "single_massless_vector_delta_neff_same_temperature": vector_same_temp_delta_neff,
        "torsion_vector_temperature_ratio_to_neutrino": torsion_vector_temperature_ratio,
        "torsion_vector_carrier_plausible": 0.7 <= torsion_vector_temperature_ratio <= 1.1,
        "immirzi_geff_carrier_plausible": required_geff_boost < 1.15,
        "preferred_next_branch": "torsion_vector_radiation_or_immirzi_geff_pre_drag",
        "is_derived_geometry": False,
        "next_required": (
            "Derive either a thermal torsion-vector radiation mode with T_T/T_nu fixed by Janus-Holst, "
            "or an Immirzi pre-drag Geff boost of the quoted size."
        ),
    }


def render_markdown(payload: dict) -> str:
    return "\n".join(
        [
            "# P0 EFT Early Deficit Carriers",
            "",
            payload["description"],
            "",
            f"Status: {payload['status']}",
            f"Derived geometry: {payload['is_derived_geometry']}",
            "",
            "## Required Deficit",
            "",
            f"- current Delta N_eff: {payload['delta_neff_current']:.6g}",
            f"- required Delta N_eff: {payload['delta_neff_required']:.6g}",
            f"- missing Delta N_eff: {payload['delta_neff_missing']:.6g}",
            f"- equivalent E^2 boost: {payload['missing_fractional_E2_on_current_radiation_branch']:.6g}",
            f"- equivalent G_eff boost: {payload['equivalent_pre_drag_Geff_boost']:.6g}",
            "",
            "## Carrier Targets",
            "",
            f"- torsion vector T_T/T_nu: {payload['torsion_vector_temperature_ratio_to_neutrino']:.6g}",
            f"- torsion vector plausible: {payload['torsion_vector_carrier_plausible']}",
            f"- Immirzi G_eff plausible: {payload['immirzi_geff_carrier_plausible']}",
            "",
            "## Next",
            "",
            payload["next_required"],
            "",
        ]
    )


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
