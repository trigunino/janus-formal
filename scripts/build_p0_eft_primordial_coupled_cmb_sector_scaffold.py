from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_primordial_coupled_cmb_sector_scaffold.md")
JSON_PATH = Path("outputs/reports/p0_eft_primordial_coupled_cmb_sector_scaffold.json")
FORTRAN_PATH = Path("external/camb_janus_fork/fortran/JanusHolstSources.f90")
TARGET_PATH = Path("outputs/reports/p0_eft_combined_primordial_sector_target.json")


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8", errors="ignore")


def build_payload() -> dict:
    source = read_text(FORTRAN_PATH)
    target = json.loads(TARGET_PATH.read_text(encoding="utf-8"))
    has_mode = "function janus_primordial_mode" in source
    sound_tied = "janus_sound_speed_factor = 1._dl + c_sound*janus_primordial_mode(a)" in source
    opacity_tied = "janus_opacity_factor = 1._dl + c_opacity*janus_primordial_mode(a)" in source
    geff_tied = "(c_geff + c_geff_background + c_coherent_immirzi)*janus_primordial_mode(a)" in source
    geff_screening_tied = "c_geff_cmb*janus_primordial_mode(a)" in source
    immirzi_tied = "janus_immirzi_activation = c_immirzi*janus_primordial_mode(a)" in source
    neutral = all(
        token in source
        for token in [
            "amp = 0.0e0_dl",
            "c_sound = 0.0e0_dl",
            "c_opacity = 0.0e0_dl",
            "c_geff = 0.0e0_dl",
            "c_immirzi = 0.0e0_dl",
        ]
    )
    scaffold_ready = all([has_mode, sound_tied, opacity_tied, geff_tied, geff_screening_tied, immirzi_tied, neutral])

    return {
        "description": "Neutral CAMB scaffold for a single coupled primordial Janus-Holst CMB sector.",
        "status": "primordial-coupled-cmb-sector-scaffold-recorded",
        "has_single_primordial_mode": has_mode,
        "sound_speed_tied_to_mode": sound_tied,
        "opacity_lowE_tied_to_mode": opacity_tied,
        "background_geff_tied_to_mode": geff_tied,
        "screened_geff_tied_to_mode": geff_screening_tied,
        "immirzi_perturbations_tied_to_mode": immirzi_tied,
        "all_amplitudes_neutral": neutral,
        "scaffold_ready": scaffold_ready,
        "required_highl_plus_lowE_suppression_fraction": target[
            "required_highl_plus_lowE_suppression_fraction"
        ],
        "strict_target_possible_without_lowlTT_lensing_work": target[
            "strict_target_possible_without_lowlTT_lensing_work"
        ],
        "derived_geometry_ready": False,
        "full_cosmology_prediction_ready_no_fit": False,
        "next_required": (
            "Derive the coefficients c_sound, c_opacity, c_geff and c_immirzi from one primordial "
            "Janus-Holst Ward identity before activating the CAMB hook."
        ),
    }


def render_markdown(payload: dict) -> str:
    return "\n".join(
        [
            "# P0 EFT Primordial Coupled CMB Sector Scaffold",
            "",
            payload["description"],
            "",
            f"Status: {payload['status']}",
            f"Scaffold ready: {payload['scaffold_ready']}",
            f"All amplitudes neutral: {payload['all_amplitudes_neutral']}",
            f"Derived geometry ready: {payload['derived_geometry_ready']}",
            f"Full no-fit ready: {payload['full_cosmology_prediction_ready_no_fit']}",
            "",
            "## Coupled Hooks",
            "",
            f"- Single primordial mode: {payload['has_single_primordial_mode']}",
            f"- Sound speed: {payload['sound_speed_tied_to_mode']}",
            f"- Opacity/lowE: {payload['opacity_lowE_tied_to_mode']}",
            f"- Background G_eff: {payload['background_geff_tied_to_mode']}",
            f"- Screened perturbative G_eff: {payload['screened_geff_tied_to_mode']}",
            f"- Immirzi perturbations: {payload['immirzi_perturbations_tied_to_mode']}",
            "",
            "## Target",
            "",
            f"- Required high-l + lowE suppression fraction: `{payload['required_highl_plus_lowE_suppression_fraction']}`",
            f"- Strict target possible without low-l/lensing work: {payload['strict_target_possible_without_lowlTT_lensing_work']}",
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
