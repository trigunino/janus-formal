from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_holst_full_stress_tensor_patch.md")
JSON_PATH = Path("outputs/reports/p0_eft_holst_full_stress_tensor_patch.json")
SOURCE_PATH = Path("external/camb_janus_fork/fortran/JanusHolstSources.f90")
EQUATIONS_PATH = Path("external/camb_janus_fork/fortran/equations.f90")


def contains(path: Path, needle: str) -> bool:
    return path.exists() and needle in path.read_text(encoding="utf-8", errors="ignore")


def build_payload() -> dict:
    components = {
        "delta_rho": contains(SOURCE_PATH, "function janus_holst_delta_rho"),
        "delta_p": contains(SOURCE_PATH, "function janus_holst_delta_p"),
        "heat_flux": contains(SOURCE_PATH, "function janus_holst_heat_flux"),
        "anisotropic_stress": contains(SOURCE_PATH, "function janus_holst_anisotropic_stress"),
    }
    injections = {
        "dgrho_constraint": contains(EQUATIONS_PATH, "dgrho = dgrho + janus_holst_delta_rho"),
        "dgq_constraint": contains(EQUATIONS_PATH, "dgq = dgq + janus_holst_heat_flux"),
        "dgpi_constraint": contains(EQUATIONS_PATH, "dgpi = dgpi + janus_holst_anisotropic_stress"),
    }
    legacy_decoupled = contains(SOURCE_PATH, "janus_immirzi_activation = c_immirzi*janus_primordial_mode(a)")
    coherent_active_path = contains(SOURCE_PATH, "c_coherent_immirzi*janus_primordial_mode(a)")
    return {
        "description": "CAMB fork audit for the full coherent Holst-Immirzi perturbative stress tensor.",
        "status": "holst-full-stress-tensor-patch-audited",
        "components": components,
        "injections": injections,
        "legacy_source_terms_decoupled": legacy_decoupled,
        "coherent_activation_path_present": coherent_active_path,
        "stress_tensor_patch_complete": all(components.values()) and all(injections.values()) and legacy_decoupled and coherent_active_path,
        "camb_patch_activated": False,
        "planck_accepted": False,
        "full_cosmology_prediction_ready_no_fit": False,
        "next_required": "Activate c_coherent_immirzi = Delta_I and rerun raw Planck likelihood.",
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Holst Full Stress Tensor Patch",
        "",
        payload["description"],
        "",
        f"Status: `{payload['status']}`",
        f"Patch complete: `{payload['stress_tensor_patch_complete']}`",
        f"CAMB patch activated: `{payload['camb_patch_activated']}`",
        f"Planck accepted: `{payload['planck_accepted']}`",
        "",
        "## Components",
        "",
    ]
    lines.extend(f"- {key}: `{value}`" for key, value in payload["components"].items())
    lines.extend(["", "## Injections", ""])
    lines.extend(f"- {key}: `{value}`" for key, value in payload["injections"].items())
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
