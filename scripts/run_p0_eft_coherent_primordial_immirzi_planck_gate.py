from __future__ import annotations

from pathlib import Path
import json
import os
import re
import subprocess
import sys


REPORT_PATH = Path("outputs/reports/p0_eft_coherent_primordial_immirzi_planck_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_coherent_primordial_immirzi_planck_gate.json")
YAML_PATH = Path("outputs/cmb_bridge/cobaya_planck_coherent_immirzi_gate.yaml")
FORK_PATH = Path("external/camb_janus_fork").resolve()
SOURCE_PATH = Path("external/camb_janus_fork/fortran/JanusHolstSources.f90")
DEFICIT_PATH = Path("outputs/reports/p0_eft_early_deficit_carriers.json")
CALIBRATION_PATH = Path("outputs/reports/p0_eft_planck_likelihood_baseline_calibration.json")


def winget_gfortran_bin() -> str | None:
    root = Path(os.environ.get("LOCALAPPDATA", "")) / "Microsoft/WinGet/Packages"
    matches = list(root.rglob("gfortran.exe")) if root.exists() else []
    return str(matches[0].parent) if matches else None


def replace_param(text: str, param_name: str, value: float) -> str:
    pattern = rf"(real\(dl\), parameter :: {re.escape(param_name)} = )[-+0-9.eE]+_dl"
    return re.sub(pattern, rf"\g<1>{value:.16e}_dl", text)


def set_coherent_immirzi(value: float) -> None:
    text = SOURCE_PATH.read_text(encoding="utf-8")
    SOURCE_PATH.write_text(replace_param(text, "c_coherent_immirzi", value), encoding="utf-8")


def build_fork() -> int:
    env = os.environ.copy()
    bin_dir = winget_gfortran_bin()
    if bin_dir:
        env["PATH"] = bin_dir + os.pathsep + env.get("PATH", "")
    result = subprocess.run(
        [sys.executable, "setup.py", "make"],
        cwd=FORK_PATH,
        text=True,
        capture_output=True,
        env=env,
        check=False,
    )
    return result.returncode


def write_yaml() -> None:
    YAML_PATH.parent.mkdir(parents=True, exist_ok=True)
    YAML_PATH.write_text(
        """\
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
  H0: 67.4
  ombh2: 0.02237
  omch2: 0.136
  tau: 0.054
  As: 2.1e-9
  ns: 0.965
  mnu: 0.06
  nnu: 3.7424238
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


def run_cobaya() -> dict:
    write_yaml()
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
        "returncode": result.returncode,
        "chi2_highl": parse(output, "planck_2018_highl_plik.TTTEEE"),
        "chi2_lowl_TT": parse(output, "planck_2018_lowl.TT"),
        "chi2_lowl_EE": parse(output, "planck_2018_lowl.EE"),
        "chi2_lensing": parse(output, "planck_2018_lensing.clik"),
        "chi2_CMB": float(total_match.group(1)) if total_match else None,
    }


def reference_chi2() -> dict[str, float]:
    calibration = json.loads(CALIBRATION_PATH.read_text(encoding="utf-8"))
    row = next(item for item in calibration["rows"] if item["name"] == "planck_lcdm_reference")
    return {
        "chi2_highl": row["chi2_highl"],
        "chi2_lowl_TT": row["chi2_lowl_TT"],
        "chi2_lowl_EE": row["chi2_lowl_EE"],
        "chi2_lensing": row["chi2_lensing"],
        "chi2_CMB": row["chi2_CMB"],
    }


def delta_i() -> float:
    payload = json.loads(DEFICIT_PATH.read_text(encoding="utf-8"))
    return float(payload["missing_fractional_E2_on_current_radiation_branch"])


def build_payload(execute: bool = True) -> dict:
    value = delta_i()
    ref = reference_chi2()
    if not execute:
        return {
            "description": "Raw Planck gate for the single-source coherent primordial Immirzi hook.",
            "status": "coherent-primordial-immirzi-planck-gate-dry",
            "c_coherent_immirzi": value,
            "reference_chi2": ref,
            "planck_accepted": False,
            "full_cosmology_prediction_ready_no_fit": False,
        }
    original = SOURCE_PATH.read_text(encoding="utf-8")
    try:
        set_coherent_immirzi(value)
        build_code = build_fork()
        result = run_cobaya() if build_code == 0 else {"returncode": build_code, "chi2_CMB": None}
    finally:
        SOURCE_PATH.write_text(original, encoding="utf-8")
        build_fork()
    deltas = {
        f"delta_{key}": result[key] - ref[key]
        for key in ref
        if result.get(key) is not None
    }
    accepted = bool(result.get("chi2_CMB") is not None and deltas.get("delta_chi2_CMB", 1e9) < 0.0)
    return {
        "description": "Raw Planck gate for the single-source coherent primordial Immirzi hook.",
        "status": "coherent-primordial-immirzi-planck-gate-run",
        "c_coherent_immirzi": value,
        "build_returncode": build_code,
        **result,
        **deltas,
        "reference_chi2": ref,
        "planck_delta_accepted": accepted,
        "full_cosmology_prediction_ready_no_fit": False,
        "next_required": "If rejected, derive a full stress-energy implementation instead of source-level hook multipliers.",
    }


def render_markdown(payload: dict) -> str:
    return "\n".join(
        [
            "# P0 EFT Coherent Primordial Immirzi Planck Gate",
            "",
            payload["description"],
            "",
            f"Status: `{payload['status']}`",
            f"c_coherent_immirzi: `{payload['c_coherent_immirzi']}`",
            f"delta chi2 CMB: `{payload.get('delta_chi2_CMB')}`",
            f"delta highl: `{payload.get('delta_chi2_highl')}`",
            f"delta lensing: `{payload.get('delta_chi2_lensing')}`",
            f"Planck delta accepted: `{payload.get('planck_delta_accepted', False)}`",
            "",
        ]
    )


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH, execute: bool = True) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload(execute=execute)
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
