from __future__ import annotations

from pathlib import Path
import json
import os
import re
import subprocess
import sys

REPORT_PATH = Path("outputs/reports/p0_eft_cmb_planck_lowl_direct_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_cmb_planck_lowl_direct_gate.json")
YAML_PATH = Path("outputs/cmb_bridge/cobaya_planck_lowl_ttee_janus_fork.yaml")
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
  planck_2018_lowl.TT: null
  planck_2018_lowl.EE: null
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


def parse_chi2(output: str, name: str) -> float | None:
    pattern = rf"chi2_{re.escape(name)}\s*=\s*([0-9.eE+-]+)"
    match = re.search(pattern, output)
    return float(match.group(1)) if match else None


def run_cobaya() -> dict:
    write_yaml()
    for lock in Path(".").glob("cobaya_planck_lowl_ttee_janus_fork*.locked"):
        lock.unlink(missing_ok=True)
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
    tt = parse_chi2(output, "planck_2018_lowl.TT")
    ee = parse_chi2(output, "planck_2018_lowl.EE")
    total_match = re.search(r"chi2__CMB\s*=\s*([0-9.eE+-]+)", output)
    total = float(total_match.group(1)) if total_match else None
    return {
        "returncode": result.returncode,
        "fork_camb_loaded": str(FORK_PATH).lower() in output.lower(),
        "chi2_planck_2018_lowl_TT": tt,
        "chi2_planck_2018_lowl_EE": ee,
        "chi2_CMB": total,
        "stdout_tail": "\n".join(output.splitlines()[-20:]),
    }


def build_payload() -> dict:
    packages_installed = PACKAGES_PATH.exists()
    fork_built = (FORK_PATH / "camb/cambdll.dll").exists()
    run = run_cobaya() if packages_installed and fork_built else None
    lowl_likelihood_run = run is not None and run["returncode"] == 0
    return {
        "description": "Direct low-ell Planck Cobaya gate using the compiled Janus-patched CAMB fork.",
        "status": "planck-lowl-direct-gate-run" if lowl_likelihood_run else "planck-lowl-direct-gate-blocked",
        "cobaya_packages_installed": packages_installed,
        "exact_camb_fork_built": fork_built,
        "yaml": str(YAML_PATH),
        "planck_lowl_likelihood_run": lowl_likelihood_run,
        "uncompressed_planck_lowl_used": lowl_likelihood_run,
        "uncompressed_planck_highl_used": False,
        "direct_cmb_likelihood_ready": False,
        "run": run,
        "next_required": "Extend this direct gate to high-ell Plik/CamSpec with nuisance handling, then evaluate full TTTEEE+lensing.",
    }


def render_markdown(payload: dict) -> str:
    run = payload["run"] or {}
    return "\n".join(
        [
            "# P0 EFT CMB Planck Low-ell Direct Gate",
            "",
            payload["description"],
            "",
            f"Status: {payload['status']}",
            f"Cobaya packages installed: {payload['cobaya_packages_installed']}",
            f"Exact CAMB fork built: {payload['exact_camb_fork_built']}",
            f"Planck low-ell likelihood run: {payload['planck_lowl_likelihood_run']}",
            f"Uncompressed Planck low-ell used: {payload['uncompressed_planck_lowl_used']}",
            f"Uncompressed Planck high-ell used: {payload['uncompressed_planck_highl_used']}",
            f"Direct CMB likelihood ready: {payload['direct_cmb_likelihood_ready']}",
            "",
            "## Chi2",
            "",
            f"- lowl TT: `{run.get('chi2_planck_2018_lowl_TT')}`",
            f"- lowl EE: `{run.get('chi2_planck_2018_lowl_EE')}`",
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
