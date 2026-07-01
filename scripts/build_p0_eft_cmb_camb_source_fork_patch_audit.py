from __future__ import annotations

from pathlib import Path
import json
import shutil
import subprocess
import os

FORK_DIR = Path("external/camb_janus_fork")
REPORT_PATH = Path("outputs/reports/p0_eft_cmb_camb_source_fork_patch_audit.md")
JSON_PATH = Path("outputs/reports/p0_eft_cmb_camb_source_fork_patch_audit.json")


def contains(path: Path, needle: str) -> bool:
    return path.exists() and needle in path.read_text(encoding="utf-8", errors="ignore")


def git_diff_names() -> list[str]:
    if not (FORK_DIR / ".git").exists():
        return []
    result = subprocess.run(
        ["git", "-C", str(FORK_DIR), "diff", "--name-only"],
        text=True,
        capture_output=True,
        check=False,
    )
    return [line.strip() for line in result.stdout.splitlines() if line.strip()]


def gfortran_path() -> str | None:
    found = shutil.which("gfortran")
    if found:
        return found
    winget_root = Path(os.environ.get("LOCALAPPDATA", "")) / "Microsoft/WinGet/Packages"
    matches = list(winget_root.rglob("gfortran.exe")) if winget_root.exists() else []
    return str(matches[0]) if matches else None


def build_payload() -> dict:
    source_clone_present = (FORK_DIR / ".git").exists()
    fortran_hook_present = (FORK_DIR / "fortran/JanusHolstSources.f90").exists()
    makefile_registered = contains(FORK_DIR / "fortran/Makefile_main", "JanusHolstSources results")
    equations_imports_hook = contains(FORK_DIR / "fortran/equations.f90", "use JanusHolstSources")
    weyl_transfer_patched = contains(
        FORK_DIR / "fortran/equations.f90",
        "EV%OutputTransfer(Transfer_Weyl) = k2*phi*janus_sigma_factor(k, a)",
    )
    lensing_source_patched = contains(
        FORK_DIR / "fortran/equations.f90",
        "EV%OutputSources(3) = -2*phi*janus_sigma_factor(k, a)*",
    )
    poisson_phi_patched = contains(
        FORK_DIR / "fortran/equations.f90",
        "phi = phi*janus_mu_factor(k, a)",
    )
    sound_speed_patched = contains(
        FORK_DIR / "fortran/equations.f90",
        "cs2 = cs2*janus_sound_speed_factor(a)",
    )
    opacity_patched = contains(
        FORK_DIR / "fortran/results.f90",
        "this%dotmu(i)=this%xe(i)*State%akthom/a2*janus_opacity_factor(a)",
    )
    geff_background_patched = contains(
        FORK_DIR / "fortran/equations.f90",
        "grhoa2 = (this%grho_no_de(a) +  grhov_t * a**2)*janus_geff_background_factor(a)",
    )
    geff_screened_perturbation_patched = contains(
        FORK_DIR / "fortran/equations.f90",
        "phi = phi*janus_mu_factor(k, a)*janus_geff_perturbation_factor(a)",
    )
    immirzi_momentum_patched = contains(
        FORK_DIR / "fortran/equations.f90",
        "janus_immirzi_momentum_source(a, dgq)",
    )
    immirzi_slip_patched = contains(
        FORK_DIR / "fortran/equations.f90",
        "slip = slip + janus_immirzi_slip_source(a, vb, qg)",
    )
    primordial_mode_present = contains(
        FORK_DIR / "fortran/JanusHolstSources.f90",
        "function janus_primordial_mode",
    )
    primordial_mode_ties_hooks = all(
        [
            contains(FORK_DIR / "fortran/JanusHolstSources.f90", "c_sound*janus_primordial_mode(a)"),
            contains(FORK_DIR / "fortran/JanusHolstSources.f90", "c_opacity*janus_primordial_mode(a)"),
            contains(FORK_DIR / "fortran/JanusHolstSources.f90", "(c_geff + c_geff_background + c_coherent_immirzi)*janus_primordial_mode(a)"),
            contains(FORK_DIR / "fortran/JanusHolstSources.f90", "c_geff_cmb*janus_primordial_mode(a)"),
            contains(FORK_DIR / "fortran/JanusHolstSources.f90", "c_immirzi*janus_primordial_mode(a)"),
        ]
    )
    compiler = gfortran_path()
    gfortran_available = compiler is not None
    camb_dll_built = (FORK_DIR / "camb/cambdll.dll").exists()
    source_patch_applied = all(
        [
            source_clone_present,
            fortran_hook_present,
            makefile_registered,
            equations_imports_hook,
            weyl_transfer_patched,
            lensing_source_patched,
            poisson_phi_patched,
            sound_speed_patched,
            opacity_patched,
            geff_background_patched,
            geff_screened_perturbation_patched,
            immirzi_momentum_patched,
            immirzi_slip_patched,
            primordial_mode_present,
            primordial_mode_ties_hooks,
        ]
    )
    return {
        "description": "Audit for the local CAMB source fork patched with Janus-Holst Weyl/lensing hooks.",
        "status": "camb-source-fork-patched-build-blocked-by-compiler"
        if source_patch_applied and not gfortran_available
        else "camb-source-fork-patch-audited",
        "source_clone_present": source_clone_present,
        "fortran_hook_present": fortran_hook_present,
        "makefile_registered": makefile_registered,
        "equations_imports_hook": equations_imports_hook,
        "weyl_transfer_patched": weyl_transfer_patched,
        "lensing_source_patched": lensing_source_patched,
        "poisson_phi_patched": poisson_phi_patched,
        "sound_speed_patched": sound_speed_patched,
        "opacity_patched": opacity_patched,
        "geff_background_patched": geff_background_patched,
        "geff_screened_perturbation_patched": geff_screened_perturbation_patched,
        "immirzi_momentum_patched": immirzi_momentum_patched,
        "immirzi_slip_patched": immirzi_slip_patched,
        "primordial_mode_present": primordial_mode_present,
        "primordial_mode_ties_hooks": primordial_mode_ties_hooks,
        "source_patch_applied": source_patch_applied,
        "gfortran_available": gfortran_available,
        "gfortran_path": compiler,
        "fork_build_attempted": camb_dll_built,
        "exact_camb_fork_built": source_patch_applied and camb_dll_built,
        "direct_cmb_likelihood_ready": False,
        "modified_files": git_diff_names(),
        "next_required": "Install gfortran, then build external/camb_janus_fork from source and replace placeholder table interpolation.",
    }


def render_markdown(payload: dict) -> str:
    return "\n".join(
        [
            "# P0 EFT CMB CAMB Source Fork Patch Audit",
            "",
            payload["description"],
            "",
            f"Status: {payload['status']}",
            f"Source clone present: {payload['source_clone_present']}",
            f"Fortran hook present: {payload['fortran_hook_present']}",
            f"Makefile registered: {payload['makefile_registered']}",
            f"Equations imports hook: {payload['equations_imports_hook']}",
            f"Weyl transfer patched: {payload['weyl_transfer_patched']}",
            f"Lensing source patched: {payload['lensing_source_patched']}",
            f"Poisson phi patched: {payload['poisson_phi_patched']}",
            f"Sound speed patched: {payload['sound_speed_patched']}",
            f"Opacity patched: {payload['opacity_patched']}",
            f"G_eff background patched: {payload['geff_background_patched']}",
            f"G_eff screened perturbation patched: {payload['geff_screened_perturbation_patched']}",
            f"Immirzi momentum patched: {payload['immirzi_momentum_patched']}",
            f"Immirzi slip patched: {payload['immirzi_slip_patched']}",
            f"Primordial mode present: {payload['primordial_mode_present']}",
            f"Primordial mode ties hooks: {payload['primordial_mode_ties_hooks']}",
            f"Source patch applied: {payload['source_patch_applied']}",
            f"gfortran available: {payload['gfortran_available']}",
            f"gfortran path: `{payload['gfortran_path']}`",
            f"Exact CAMB fork built: {payload['exact_camb_fork_built']}",
            f"Direct CMB likelihood ready: {payload['direct_cmb_likelihood_ready']}",
            "",
            "## Modified fork files",
            "",
            *[f"- `{name}`" for name in payload["modified_files"]],
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
