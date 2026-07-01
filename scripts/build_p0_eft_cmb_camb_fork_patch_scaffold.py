from __future__ import annotations

from pathlib import Path
import importlib.util
import json

PATCH_DIR = Path("outputs/cmb_bridge/camb_fork_patch")
REPORT_PATH = Path("outputs/reports/p0_eft_cmb_camb_fork_patch_scaffold.md")
JSON_PATH = Path("outputs/reports/p0_eft_cmb_camb_fork_patch_scaffold.json")


FORTRAN_STUB = """\
! Janus-Holst CAMB fork hook scaffold.
! This file is intended for a CAMB source checkout, not the pip wheel DLL.
module JanusHolstSources
  implicit none
  private
  public :: janus_sigma_factor, janus_mu_factor

contains

  real(8) function janus_sigma_factor(k, a)
    real(8), intent(in) :: k, a
    ! TODO(fork): replace this placeholder by table interpolation from
    ! janus_holst_mu_sigma.csv during CAMB source evolution.
    janus_sigma_factor = 1.0d0
  end function janus_sigma_factor

  real(8) function janus_mu_factor(k, a)
    real(8), intent(in) :: k, a
    ! TODO(fork): replace this placeholder by table interpolation from
    ! janus_holst_mu_sigma.csv during CAMB source evolution.
    janus_mu_factor = 1.0d0
  end function janus_mu_factor

end module JanusHolstSources
"""


PYTHON_HOOK = """\
from __future__ import annotations

from pathlib import Path
import csv


def load_janus_mu_sigma(path: str | Path) -> list[dict[str, float]]:
    with Path(path).open(newline="", encoding="utf-8") as handle:
        return [{k: float(v) for k, v in row.items()} for row in csv.DictReader(handle)]


def validate_janus_mu_sigma(rows: list[dict[str, float]]) -> None:
    required = {"k", "a", "mu_JH", "Sigma_JH"}
    if not rows or set(rows[0]) != required:
        raise ValueError("Expected columns k,a,mu_JH,Sigma_JH")
    if any(row["k"] <= 0 or row["a"] <= 0 for row in rows):
        raise ValueError("k and a must be positive")


def prepare_fortran_table_payload(path: str | Path) -> dict[str, object]:
    rows = load_janus_mu_sigma(path)
    validate_janus_mu_sigma(rows)
    return {
        "row_count": len(rows),
        "k_values": sorted({row["k"] for row in rows}),
        "a_values": sorted({row["a"] for row in rows}),
    }
"""


README = """\
# Janus-Holst CAMB Fork Patch Scaffold

This directory is a patch scaffold for a CAMB **source checkout**.
The installed Python wheel in this environment is a compiled DLL and has no
Fortran sources to patch in place.

Required fork work:

1. Add `JanusHolstSources.f90` to the CAMB source tree.
2. Replace the placeholder `janus_mu_factor(k,a)` and
   `janus_sigma_factor(k,a)` with interpolation over
   `outputs/cmb_bridge/janus_holst_mu_sigma.csv`.
3. Call these factors inside CAMB scalar perturbation/source evolution, before
   TT/TE/EE/lensing spectra are projected.
4. Rebuild CAMB from source.
5. Compare against uncompressed Planck likelihoods.

Until step 3 is done inside CAMB evolution, `direct_cmb_likelihood_ready`
must remain false.
"""


def camb_wheel_has_fortran_sources() -> bool:
    spec = importlib.util.find_spec("camb")
    if spec is None or spec.origin is None:
        return False
    package_dir = Path(spec.origin).parent
    return any(package_dir.rglob("*.f90")) or any(package_dir.rglob("*.F90"))


def write_patch_files() -> dict[str, str]:
    PATCH_DIR.mkdir(parents=True, exist_ok=True)
    files = {
        "fortran_stub": PATCH_DIR / "JanusHolstSources.f90",
        "python_hook": PATCH_DIR / "janus_holst_table_hook.py",
        "readme": PATCH_DIR / "README.md",
    }
    files["fortran_stub"].write_text(FORTRAN_STUB, encoding="utf-8")
    files["python_hook"].write_text(PYTHON_HOOK, encoding="utf-8")
    files["readme"].write_text(README, encoding="utf-8")
    return {key: str(path) for key, path in files.items()}


def build_payload() -> dict:
    files = write_patch_files()
    source_patchable = camb_wheel_has_fortran_sources()
    return {
        "description": "CAMB source-fork patch scaffold for injecting Janus-Holst mu/Sigma during Boltzmann evolution.",
        "status": "camb-fork-patch-scaffold-written",
        "installed_camb_wheel_source_patchable": source_patchable,
        "patch_scaffold_written": True,
        "fortran_hook_scaffold_written": True,
        "python_table_hook_written": True,
        "exact_camb_fork_built": False,
        "boltzmann_equations_modified_in_solver": False,
        "direct_cmb_likelihood_ready": False,
        "files": files,
        "next_required": "Apply this scaffold to a CAMB source checkout and patch scalar source evolution in Fortran.",
    }


def render_markdown(payload: dict) -> str:
    return "\n".join(
        [
            "# P0 EFT CMB CAMB Fork Patch Scaffold",
            "",
            payload["description"],
            "",
            f"Status: {payload['status']}",
            f"Installed CAMB wheel source patchable: {payload['installed_camb_wheel_source_patchable']}",
            f"Patch scaffold written: {payload['patch_scaffold_written']}",
            f"Exact CAMB fork built: {payload['exact_camb_fork_built']}",
            f"Boltzmann equations modified in solver: {payload['boltzmann_equations_modified_in_solver']}",
            f"Direct CMB likelihood ready: {payload['direct_cmb_likelihood_ready']}",
            "",
            "## Files",
            "",
            *[f"- {name}: `{path}`" for name, path in payload["files"].items()],
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
    print(f"Wrote {PATCH_DIR}")


if __name__ == "__main__":
    main()
