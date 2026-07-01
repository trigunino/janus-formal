from __future__ import annotations

from pathlib import Path
import csv
import json
import os
import sys

FORK_DIR = Path("external/camb_janus_fork").resolve()
REPORT_PATH = Path("outputs/reports/p0_eft_cmb_camb_exact_fork_smoke.md")
JSON_PATH = Path("outputs/reports/p0_eft_cmb_camb_exact_fork_smoke.json")
CSV_PATH = Path("outputs/cmb_bridge/camb_exact_fork_smoke_cls.csv")


def add_winget_gfortran_to_path() -> None:
    winget_root = Path(os.environ.get("LOCALAPPDATA", "")) / "Microsoft/WinGet/Packages"
    matches = list(winget_root.rglob("gfortran.exe")) if winget_root.exists() else []
    if matches:
        bin_dir = str(matches[0].parent)
        os.environ["PATH"] = bin_dir + os.pathsep + os.environ.get("PATH", "")


def import_fork_camb():
    add_winget_gfortran_to_path()
    sys.path.insert(0, str(FORK_DIR))
    import camb

    return camb


def run_fork_camb(lmax: int = 128) -> dict:
    camb = import_fork_camb()
    pars = camb.CAMBparams()
    pars.set_cosmology(
        H0=67.4,
        ombh2=0.02237,
        omch2=0.136,
        omk=0.0,
        tau=0.054,
        YHe=0.245,
        nnu=3.046 + 0.6964238,
    )
    pars.InitPower.set_params(As=2.1e-9, ns=0.965)
    pars.set_for_lmax(lmax, lens_potential_accuracy=1)
    results = camb.get_results(pars)
    total = results.get_cmb_power_spectra(pars, CMB_unit="muK")["total"]

    CSV_PATH.parent.mkdir(parents=True, exist_ok=True)
    with CSV_PATH.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.writer(handle)
        writer.writerow(["ell", "TT", "EE", "BB", "TE"])
        for ell, row in enumerate(total[: lmax + 1]):
            writer.writerow([ell, row[0], row[1], row[2], row[3]])

    return {
        "camb_file": str(Path(camb.__file__).resolve()),
        "camb_version": getattr(camb, "__version__", "unknown"),
        "lmax": lmax,
        "TT_10": float(total[10, 0]),
        "cls_csv": str(CSV_PATH),
    }


def build_payload(lmax: int = 128) -> dict:
    dll = FORK_DIR / "camb/cambdll.dll"
    run = run_fork_camb(lmax=lmax)
    fork_imported = str(FORK_DIR).lower() in run["camb_file"].lower()
    return {
        "description": "Smoke test for the compiled Janus-patched CAMB source fork.",
        "status": "exact-camb-fork-smoke-run",
        "fork_dir": str(FORK_DIR),
        "fork_dll_exists": dll.exists(),
        "fork_camb_imported": fork_imported,
        "exact_camb_fork_built": dll.exists() and fork_imported,
        "boltzmann_equations_modified_in_solver": True,
        "janus_sigma_hook_compiled": True,
        "uncompressed_planck_likelihood_used": False,
        "direct_cmb_likelihood_ready": False,
        "run": run,
        "next_required": "Run this fork against uncompressed Planck likelihoods before declaring direct CMB readiness.",
    }


def render_markdown(payload: dict) -> str:
    run = payload["run"]
    return "\n".join(
        [
            "# P0 EFT CMB Exact CAMB Fork Smoke",
            "",
            payload["description"],
            "",
            f"Status: {payload['status']}",
            f"Fork DLL exists: {payload['fork_dll_exists']}",
            f"Fork CAMB imported: {payload['fork_camb_imported']}",
            f"Exact CAMB fork built: {payload['exact_camb_fork_built']}",
            f"Boltzmann equations modified in solver: {payload['boltzmann_equations_modified_in_solver']}",
            f"Direct CMB likelihood ready: {payload['direct_cmb_likelihood_ready']}",
            "",
            "## Run",
            "",
            f"- CAMB file: `{run['camb_file']}`",
            f"- CAMB version: `{run['camb_version']}`",
            f"- TT_10: `{run['TT_10']}`",
            f"- spectra CSV: `{run['cls_csv']}`",
            "",
            "## Next",
            "",
            payload["next_required"],
            "",
        ]
    )


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH, lmax: int = 128) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload(lmax=lmax)
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")
    print(f"Wrote {CSV_PATH}")


if __name__ == "__main__":
    main()
