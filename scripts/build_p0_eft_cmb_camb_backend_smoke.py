from __future__ import annotations

from pathlib import Path
import csv
import importlib.util
import json

REPORT_PATH = Path("outputs/reports/p0_eft_cmb_camb_backend_smoke.md")
JSON_PATH = Path("outputs/reports/p0_eft_cmb_camb_backend_smoke.json")
CSV_PATH = Path("outputs/cmb_bridge/camb_backend_smoke_cls.csv")

OMEGA_M0_JANUS = 0.3482119
DELTA_NEFF_HOLST = 0.6964238
H0 = 67.4
OMBH2 = 0.02237
TAU = 0.054
AS = 2.1e-9
NS = 0.965


def camb_available() -> bool:
    return importlib.util.find_spec("camb") is not None


def run_camb(lmax: int = 800) -> dict:
    import camb

    h = H0 / 100.0
    ommh2 = OMEGA_M0_JANUS * h * h
    omch2 = max(ommh2 - OMBH2, 1.0e-6)

    pars = camb.CAMBparams()
    pars.set_cosmology(
        H0=H0,
        ombh2=OMBH2,
        omch2=omch2,
        omk=0.0,
        tau=TAU,
        mnu=0.06,
        nnu=3.046 + DELTA_NEFF_HOLST,
        YHe=0.245,
    )
    pars.InitPower.set_params(As=AS, ns=NS)
    pars.set_for_lmax(lmax, lens_potential_accuracy=1)
    pars.set_matter_power(redshifts=[0.0], kmax=2.0)

    results = camb.get_results(pars)
    spectra = results.get_cmb_power_spectra(pars, CMB_unit="muK")
    total = spectra["total"]

    CSV_PATH.parent.mkdir(parents=True, exist_ok=True)
    with CSV_PATH.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.writer(handle)
        writer.writerow(["ell", "TT", "EE", "BB", "TE"])
        for ell, row in enumerate(total[: lmax + 1]):
            writer.writerow([ell, row[0], row[1], row[2], row[3]])

    return {
        "camb_version": getattr(camb, "__version__", "unknown"),
        "lmax": lmax,
        "H0": H0,
        "Omega_m0": OMEGA_M0_JANUS,
        "ombh2": OMBH2,
        "omch2": omch2,
        "Delta_Neff_Holst": DELTA_NEFF_HOLST,
        "N_eff": 3.046 + DELTA_NEFF_HOLST,
        "sigma8": [float(x) for x in results.get_sigma8()],
        "cls_csv": str(CSV_PATH),
    }


def build_payload(lmax: int = 800) -> dict:
    available = camb_available()
    camb_run = run_camb(lmax=lmax) if available else None
    payload = {
        "description": "Real CAMB backend smoke run for the Janus-Holst CMB bridge.",
        "status": "camb-backend-smoke-run" if available else "camb-backend-missing",
        "python_camb_available": available,
        "backend_solver_run": available,
        "janus_background_parameters_injected": available,
        "janus_modified_gravity_tables_injected": False,
        "uncompressed_planck_likelihood_used": False,
        "direct_cmb_likelihood_ready": False,
        "camb_run": camb_run,
        "next_required": (
            "Implement a CAMB fork/wrapper that consumes Janus mu/Sigma/background tables, "
            "then compare against uncompressed Planck likelihoods."
        ),
    }
    return payload


def render_markdown(payload: dict) -> str:
    camb_run = payload["camb_run"] or {}
    return "\n".join(
        [
            "# P0 EFT CMB CAMB Backend Smoke",
            "",
            payload["description"],
            "",
            f"Status: {payload['status']}",
            f"Python CAMB available: {payload['python_camb_available']}",
            f"Backend solver run: {payload['backend_solver_run']}",
            f"Janus background parameters injected: {payload['janus_background_parameters_injected']}",
            f"Janus modified-gravity tables injected: {payload['janus_modified_gravity_tables_injected']}",
            f"Direct CMB likelihood ready: {payload['direct_cmb_likelihood_ready']}",
            "",
            "## CAMB Run",
            "",
            f"- version: `{camb_run.get('camb_version', 'n/a')}`",
            f"- lmax: `{camb_run.get('lmax', 'n/a')}`",
            f"- Omega_m0: `{camb_run.get('Omega_m0', 'n/a')}`",
            f"- Delta_Neff_Holst: `{camb_run.get('Delta_Neff_Holst', 'n/a')}`",
            f"- spectra CSV: `{camb_run.get('cls_csv', 'n/a')}`",
            "",
            "## Next",
            "",
            payload["next_required"],
            "",
        ]
    )


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH, lmax: int = 800) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload(lmax=lmax)
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")
    if CSV_PATH.exists():
        print(f"Wrote {CSV_PATH}")


if __name__ == "__main__":
    main()
