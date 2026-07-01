from __future__ import annotations

from pathlib import Path
import json
import os
import re
import subprocess
import sys


REPORT_PATH = Path("outputs/reports/p0_eft_planck_likelihood_baseline_calibration.md")
JSON_PATH = Path("outputs/reports/p0_eft_planck_likelihood_baseline_calibration.json")
YAML_PATH = Path("outputs/cmb_bridge/cobaya_planck_baseline_calibration.yaml")
FORK_PATH = Path("external/camb_janus_fork").resolve()

POINTS = {
    "planck_lcdm_reference": {
        "H0": 67.36,
        "ombh2": 0.02237,
        "omch2": 0.1200,
        "tau": 0.0544,
        "As": 2.1e-9,
        "ns": 0.9649,
        "nnu": 3.044,
    },
    "janus_cmb_working_point": {
        "H0": 67.4,
        "ombh2": 0.02237,
        "omch2": 0.136,
        "tau": 0.054,
        "As": 2.1e-9,
        "ns": 0.965,
        "nnu": 3.7424238,
    },
}


def winget_gfortran_bin() -> str | None:
    root = Path(os.environ.get("LOCALAPPDATA", "")) / "Microsoft/WinGet/Packages"
    matches = list(root.rglob("gfortran.exe")) if root.exists() else []
    return str(matches[0].parent) if matches else None


def write_yaml(params: dict[str, float]) -> None:
    YAML_PATH.parent.mkdir(parents=True, exist_ok=True)
    YAML_PATH.write_text(
        f"""\
output: null
theory:
  camb:
    extra_args:
      lens_potential_accuracy: 1
likelihood:
  planck_2018_highl_plik.TTTEEE: null
  planck_2018_lowl.TT: null
  planck_2018_lowl.EE: null
  planck_2018_lensing.clik: null
params:
  H0: {params["H0"]}
  ombh2: {params["ombh2"]}
  omch2: {params["omch2"]}
  tau: {params["tau"]}
  As: {params["As"]}
  ns: {params["ns"]}
  mnu: 0.06
  nnu: {params["nnu"]}
  omk: 0
  YHe: 0.245
sampler:
  evaluate: null
packages_path: external/cobaya_packages
""",
        encoding="utf-8",
    )


def parse(output: str, label: str) -> float | None:
    match = re.search(rf"chi2_{re.escape(label)}\s*=\s*([0-9.eE+-]+)", output)
    return float(match.group(1)) if match else None


def evaluate(name: str, params: dict[str, float]) -> dict:
    write_yaml(params)
    env = os.environ.copy()
    env["PYTHONPATH"] = str(FORK_PATH) + os.pathsep + env.get("PYTHONPATH", "")
    bin_dir = winget_gfortran_bin()
    if bin_dir:
        env["PATH"] = bin_dir + os.pathsep + env.get("PATH", "")
    result = subprocess.run(
        [sys.executable, "-m", "cobaya", "run", str(YAML_PATH), "-f"],
        text=True,
        capture_output=True,
        env=env,
        check=False,
    )
    output = result.stdout + result.stderr
    total_match = re.search(r"chi2__CMB\s*=\s*([0-9.eE+-]+)", output)
    return {
        "name": name,
        "returncode": result.returncode,
        "params": params,
        "chi2_highl": parse(output, "planck_2018_highl_plik.TTTEEE"),
        "chi2_lowl_TT": parse(output, "planck_2018_lowl.TT"),
        "chi2_lowl_EE": parse(output, "planck_2018_lowl.EE"),
        "chi2_lensing": parse(output, "planck_2018_lensing.clik"),
        "chi2_CMB": float(total_match.group(1)) if total_match else None,
    }


def build_payload() -> dict:
    rows = [evaluate(name, params) for name, params in POINTS.items()]
    by_name = {row["name"]: row for row in rows}
    ref = by_name["planck_lcdm_reference"]
    janus = by_name["janus_cmb_working_point"]
    deltas = {
        key: (janus[key] - ref[key])
        for key in ["chi2_highl", "chi2_lowl_TT", "chi2_lowl_EE", "chi2_lensing", "chi2_CMB"]
        if janus[key] is not None and ref[key] is not None
    }
    return {
        "description": "Planck likelihood absolute-offset calibration for Janus CMB diagnostics.",
        "status": "planck-likelihood-baseline-calibration-run",
        "method_guard": (
            "The LCDM point is not used as observational evidence for Janus. It is only a numerical "
            "zero-point calibration for absolute Cobaya/Planck likelihood offsets."
        ),
        "uses_lcdm_compressed_parameters_as_data": False,
        "raw_planck_likelihood_used": True,
        "rows": rows,
        "deltas_janus_minus_reference": deltas,
        "lowE_absolute_offset_is_normal": abs(deltas.get("chi2_lowl_EE", 999.0)) < 10.0,
        "primary_blocker": max(deltas, key=lambda key: deltas[key]) if deltas else None,
        "full_cosmology_prediction_ready_no_fit": False,
        "next_required": "Use delta-chi2 diagnostics. Do not treat Planck lowE absolute chi2 offset as a physical failure.",
    }


def render_markdown(payload: dict) -> str:
    return "\n".join(
        [
            "# P0 EFT Planck Likelihood Baseline Calibration",
            "",
            payload["description"],
            "",
            f"Status: {payload['status']}",
            f"Uses LCDM compressed parameters as data: {payload['uses_lcdm_compressed_parameters_as_data']}",
            f"Raw Planck likelihood used: {payload['raw_planck_likelihood_used']}",
            f"lowE absolute offset normal: {payload['lowE_absolute_offset_is_normal']}",
            f"Primary blocker: `{payload['primary_blocker']}`",
            f"Full no-fit ready: {payload['full_cosmology_prediction_ready_no_fit']}",
            "",
            "## Guard",
            "",
            payload["method_guard"],
            "",
            "## Delta chi2 Janus - Reference",
            "",
            *[f"- `{key}`: `{value}`" for key, value in payload["deltas_janus_minus_reference"].items()],
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
