from __future__ import annotations

from pathlib import Path
import json
import os
import re
import subprocess
import sys


REPORT_PATH = Path("outputs/reports/p0_eft_lowe_tau_rescue_scan.md")
JSON_PATH = Path("outputs/reports/p0_eft_lowe_tau_rescue_scan.json")
CSV_PATH = Path("outputs/reports/p0_eft_lowe_tau_rescue_scan.csv")
YAML_PATH = Path("outputs/cmb_bridge/cobaya_lowe_tau_rescue_scan.yaml")
FORK_PATH = Path("external/camb_janus_fork").resolve()

BASE = {
    "H0": 67.4,
    "ombh2": 0.0224,
    "omch2": 0.136,
    "As": 2.1e-9,
    "ns": 0.94,
    "nnu": 3.7424238,
}
TAU_GRID = [0.03, 0.035, 0.04, 0.045, 0.05, 0.055, 0.06, 0.065, 0.07]


def winget_gfortran_bin() -> str | None:
    root = Path(os.environ.get("LOCALAPPDATA", "")) / "Microsoft/WinGet/Packages"
    matches = list(root.rglob("gfortran.exe")) if root.exists() else []
    return str(matches[0].parent) if matches else None


def write_yaml(tau: float) -> None:
    YAML_PATH.parent.mkdir(parents=True, exist_ok=True)
    YAML_PATH.write_text(
        f"""\
output: null
theory:
  camb:
    extra_args:
      lens_potential_accuracy: 1
likelihood:
  planck_2018_lowl.EE: null
params:
  H0: {BASE["H0"]}
  ombh2: {BASE["ombh2"]}
  omch2: {BASE["omch2"]}
  tau: {tau}
  As: {BASE["As"]}
  ns: {BASE["ns"]}
  mnu: 0.06
  nnu: {BASE["nnu"]}
  omk: 0
  YHe: 0.245
sampler:
  evaluate: null
packages_path: external/cobaya_packages
""",
        encoding="utf-8",
    )


def parse_chi2(output: str) -> float | None:
    match = re.search(r"chi2_planck_2018_lowl\.EE\s*=\s*([0-9.eE+-]+)", output)
    return float(match.group(1)) if match else None


def run_tau(tau: float) -> dict:
    write_yaml(tau)
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
    return {
        "tau": tau,
        "returncode": result.returncode,
        "fork_camb_loaded": str(FORK_PATH).lower() in output.lower(),
        "chi2_lowl_EE": parse_chi2(output),
    }


def build_payload() -> dict:
    rows = [run_tau(tau) for tau in TAU_GRID]
    valid = [row for row in rows if row["chi2_lowl_EE"] is not None]
    best = min(valid, key=lambda row: row["chi2_lowl_EE"]) if valid else None
    lowe_tau_can_be_tuned = bool(best and best["chi2_lowl_EE"] < 50.0)
    CSV_PATH.parent.mkdir(parents=True, exist_ok=True)
    headers = ["tau", "chi2_lowl_EE", "returncode", "fork_camb_loaded"]
    CSV_PATH.write_text(
        "\n".join([",".join(headers)] + [",".join(str(row.get(h, "")) for h in headers) for row in rows]) + "\n",
        encoding="utf-8",
    )
    return {
        "description": "LowE-only tau rescue scan for the Janus-Holst CMB branch.",
        "status": "lowe-tau-rescue-scan-run",
        "tau_grid": TAU_GRID,
        "rows": rows,
        "valid_points": len(valid),
        "best": best,
        "lowe_tau_can_be_tuned": lowe_tau_can_be_tuned,
        "full_cosmology_prediction_ready_no_fit": False,
        "csv": str(CSV_PATH),
        "next_required": (
            "Tau-only reionization is excluded; derive a nonstandard lowE source shape together with "
            "a pre-recombination high-l transfer sector."
            if not lowe_tau_can_be_tuned
            else "Derive tau from Janus reionization geometry; high-l still needs a primordial transfer sector."
        ),
    }


def render_markdown(payload: dict) -> str:
    best = payload["best"] or {}
    return "\n".join(
        [
            "# P0 EFT lowE Tau Rescue Scan",
            "",
            payload["description"],
            "",
            f"Status: {payload['status']}",
            f"Best tau: `{best.get('tau')}`",
            f"Best lowE EE chi2: `{best.get('chi2_lowl_EE')}`",
            f"lowE tau can be tuned: {payload['lowe_tau_can_be_tuned']}",
            f"Full no-fit ready: {payload['full_cosmology_prediction_ready_no_fit']}",
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
    print(f"Wrote {CSV_PATH}")


if __name__ == "__main__":
    main()
