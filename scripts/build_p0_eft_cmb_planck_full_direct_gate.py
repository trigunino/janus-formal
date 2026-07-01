from __future__ import annotations

from pathlib import Path
import json
import os
import re
import subprocess
import sys

REPORT_PATH = Path("outputs/reports/p0_eft_cmb_planck_full_direct_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_cmb_planck_full_direct_gate.json")
YAML_PATH = Path("outputs/cmb_bridge/cobaya_planck_full_janus_fork.yaml")
PACKAGES_PATH = Path("external/cobaya_packages")
FORK_PATH = Path("external/camb_janus_fork").resolve()


def winget_gfortran_bin() -> str | None:
    root = Path(os.environ.get("LOCALAPPDATA", "")) / "Microsoft/WinGet/Packages"
    matches = list(root.rglob("gfortran.exe")) if root.exists() else []
    return str(matches[0].parent) if matches else None


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


def parse_chi2(output: str, label: str) -> float | None:
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
        "fork_camb_loaded": str(FORK_PATH).lower() in output.lower(),
        "clipy_loaded": "clipy" in output.lower(),
        "chi2_highl_plik_TTTEEE": parse_chi2(output, "planck_2018_highl_plik.TTTEEE"),
        "chi2_lowl_TT": parse_chi2(output, "planck_2018_lowl.TT"),
        "chi2_lowl_EE": parse_chi2(output, "planck_2018_lowl.EE"),
        "chi2_lensing": parse_chi2(output, "planck_2018_lensing.clik"),
        "chi2_CMB": float(total_match.group(1)) if total_match else None,
        "stdout_tail": "\n".join(output.splitlines()[-24:]),
    }


def build_payload() -> dict:
    packages_installed = PACKAGES_PATH.exists()
    fork_built = (FORK_PATH / "camb/cambdll.dll").exists()
    run = run_cobaya() if packages_installed and fork_built else None
    full_run = run is not None and run["returncode"] == 0
    passed_reference_gate = bool(full_run and run["chi2_CMB"] is not None and run["chi2_CMB"] < 2000.0)
    return {
        "description": "Full direct Planck Cobaya gate using the compiled Janus-patched CAMB fork.",
        "status": "planck-full-direct-gate-run",
        "cobaya_packages_installed": packages_installed,
        "exact_camb_fork_built": fork_built,
        "yaml": str(YAML_PATH),
        "full_planck_likelihood_run": full_run,
        "uncompressed_planck_highl_used": full_run,
        "uncompressed_planck_lowl_used": full_run,
        "uncompressed_planck_lensing_used": full_run,
        "passed_reference_gate": passed_reference_gate,
        "direct_cmb_likelihood_ready": full_run,
        "cmb_observationally_accepted": passed_reference_gate,
        "run": run,
        "next_required": "Refit/derive Janus CMB-sector parameters against the full Planck likelihood; current fixed branch is rejected.",
    }


def render_markdown(payload: dict) -> str:
    run = payload["run"] or {}
    return "\n".join(
        [
            "# P0 EFT CMB Planck Full Direct Gate",
            "",
            payload["description"],
            "",
            f"Status: {payload['status']}",
            f"Exact CAMB fork built: {payload['exact_camb_fork_built']}",
            f"Full Planck likelihood run: {payload['full_planck_likelihood_run']}",
            f"Direct CMB likelihood ready: {payload['direct_cmb_likelihood_ready']}",
            f"CMB observationally accepted: {payload['cmb_observationally_accepted']}",
            "",
            "## Chi2",
            "",
            f"- highl Plik TTTEEE: `{run.get('chi2_highl_plik_TTTEEE')}`",
            f"- lowl TT: `{run.get('chi2_lowl_TT')}`",
            f"- lowl EE: `{run.get('chi2_lowl_EE')}`",
            f"- lensing: `{run.get('chi2_lensing')}`",
            f"- total CMB: `{run.get('chi2_CMB')}`",
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
