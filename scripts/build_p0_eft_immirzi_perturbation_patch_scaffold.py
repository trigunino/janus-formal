from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_immirzi_perturbation_patch_scaffold.md")
JSON_PATH = Path("outputs/reports/p0_eft_immirzi_perturbation_patch_scaffold.json")
EQUATIONS_PATH = Path("external/camb_janus_fork/fortran/equations.f90")
SOURCES_PATH = Path("external/camb_janus_fork/fortran/JanusHolstSources.f90")


def contains(path: Path, needle: str) -> bool:
    return path.exists() and needle in path.read_text(encoding="utf-8", errors="ignore")


def build_payload() -> dict:
    obligations = [
        {
            "name": "background_dtauda",
            "hook": "janus_geff_factor(a)",
            "location": "equations.f90:dtauda",
            "implemented": contains(EQUATIONS_PATH, "janus_geff_factor(a)"),
            "active": contains(SOURCES_PATH, "real(dl), parameter :: amp = 9.778424139658529e-2_dl"),
        },
        {
            "name": "poisson_phi_constraint",
            "hook": "janus_mu_factor(k, a)",
            "location": "equations.f90:phi constraint",
            "implemented": contains(EQUATIONS_PATH, "phi = phi*janus_mu_factor(k, a)"),
            "active": True,
        },
        {
            "name": "momentum_constraint_sigma_etak",
            "hook": "missing Immirzi momentum source",
            "location": "equations.f90:sigma/etak constraints",
            "implemented": False,
            "active": False,
        },
        {
            "name": "anisotropic_stress_dgpi",
            "hook": "missing Immirzi shear stress source",
            "location": "equations.f90:dgpi/diff_rhopi",
            "implemented": False,
            "active": False,
        },
        {
            "name": "photon_baryon_slip",
            "hook": "missing Immirzi slip/friction source",
            "location": "equations.f90:qgdot/vbdot/slip",
            "implemented": False,
            "active": False,
        },
    ]
    missing = [item["name"] for item in obligations if not item["implemented"]]
    return {
        "description": "Scaffold for a consistent Immirzi perturbation-sector CAMB patch.",
        "status": "immirzi-perturbation-patch-scaffolded",
        "obligations": obligations,
        "missing_obligations": missing,
        "background_only_patch_rejected": True,
        "consistent_perturbation_sector_ready": len(missing) == 0,
        "safe_to_activate_geff_background": False,
        "next_required": (
            "Derive the Immirzi contributions to momentum constraint, anisotropic stress, "
            "and photon-baryon slip before enabling a nonzero G_eff background amplitude."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Immirzi Perturbation Patch Scaffold",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Consistent sector ready: {payload['consistent_perturbation_sector_ready']}",
        f"Safe to activate G_eff background: {payload['safe_to_activate_geff_background']}",
        "",
        "| obligation | location | implemented | active |",
        "|---|---|---:|---:|",
    ]
    for item in payload["obligations"]:
        lines.append(
            f"| {item['name']} | {item['location']} | {item['implemented']} | {item['active']} |"
        )
    lines.extend(["", "## Missing", "", *[f"- `{name}`" for name in payload["missing_obligations"]], ""])
    lines.extend(["## Next", "", payload["next_required"], ""])
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
