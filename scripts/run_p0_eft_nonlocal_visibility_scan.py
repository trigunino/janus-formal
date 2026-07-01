from __future__ import annotations

from pathlib import Path
import json
import os
import re
import subprocess
import sys


REPORT_PATH = Path("outputs/reports/p0_eft_nonlocal_visibility_scan.md")
JSON_PATH = Path("outputs/reports/p0_eft_nonlocal_visibility_scan.json")
CSV_PATH = Path("outputs/reports/p0_eft_nonlocal_visibility_scan.csv")
YAML_PATH = Path("outputs/cmb_bridge/cobaya_planck_nonlocal_visibility_scan.yaml")
FORK_PATH = Path("external/camb_janus_fork").resolve()
SOURCE_PATH = Path("external/camb_janus_fork/fortran/JanusHolstSources.f90")
VISIBILITY_MEMORY_GRID = [-0.5, -0.25, 0.0, 0.25, 0.5]


def winget_gfortran_bin() -> str | None:
    root = Path(os.environ.get("LOCALAPPDATA", "")) / "Microsoft/WinGet/Packages"
    matches = list(root.rglob("gfortran.exe")) if root.exists() else []
    return str(matches[0].parent) if matches else None


def replace_param(text: str, param_name: str, value: float) -> str:
    pattern = rf"(real\(dl\), parameter :: {re.escape(param_name)} = )[-+0-9.eE]+_dl"
    return re.sub(pattern, rf"\g<1>{value:.16e}_dl", text)


def set_visibility_memory(amplitude: float) -> None:
    text = SOURCE_PATH.read_text(encoding="utf-8")
    text = replace_param(text, "c_visibility_memory", amplitude)
    SOURCE_PATH.write_text(text, encoding="utf-8")


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


def run_point(amplitude: float) -> dict:
    set_visibility_memory(amplitude)
    build_code = build_fork()
    result = run_cobaya() if build_code == 0 else {"returncode": build_code, "chi2_CMB": None}
    return {"c_visibility_memory": amplitude, "build_returncode": build_code, **result}


def build_payload(points: list[float] | None = None, execute: bool = True) -> dict:
    points = points or VISIBILITY_MEMORY_GRID
    if not execute:
        rows = [{"c_visibility_memory": point} for point in points]
        return {
            "description": "Nonlocal visibility-memory scan for the Janus-Holst CMB lowE route.",
            "status": "nonlocal-visibility-scan-dry",
            "grid_size": len(points),
            "valid_points": 0,
            "rows": rows,
            "best": None,
            "planck_accepted": False,
            "full_cosmology_prediction_ready_no_fit": False,
            "next_required": "If visibility memory helps lowE without damaging high-l, derive its kernel from Janus geometry.",
        }
    original = SOURCE_PATH.read_text(encoding="utf-8")
    rows: list[dict] = []
    try:
        rows = [run_point(point) for point in points]
    finally:
        SOURCE_PATH.write_text(original, encoding="utf-8")
        build_fork()
    valid = [row for row in rows if row.get("returncode") == 0 and row.get("chi2_CMB") is not None]
    best = min(valid, key=lambda row: row["chi2_CMB"]) if valid else None
    return {
        "description": "Nonlocal visibility-memory scan for the Janus-Holst CMB lowE route.",
        "status": "nonlocal-visibility-scan-run" if execute else "nonlocal-visibility-scan-dry",
        "grid_size": len(points),
        "valid_points": len(valid),
        "rows": rows,
        "best": best,
        "planck_accepted": bool(best and best["chi2_CMB"] < 2000.0),
        "full_cosmology_prediction_ready_no_fit": False,
        "next_required": "If visibility memory helps lowE without damaging high-l, derive its kernel from Janus geometry.",
    }


def render_markdown(payload: dict) -> str:
    best = payload["best"] or {}
    return "\n".join(
        [
            "# P0 EFT Nonlocal Visibility Scan",
            "",
            payload["description"],
            "",
            f"Status: {payload['status']}",
            f"Valid points: {payload['valid_points']}",
            f"Planck accepted: {payload['planck_accepted']}",
            "",
            "## Best",
            "",
            f"- c_visibility_memory: `{best.get('c_visibility_memory')}`",
            f"- chi2 CMB: `{best.get('chi2_CMB')}`",
            f"- highl: `{best.get('chi2_highl')}`",
            f"- lowE: `{best.get('chi2_lowl_EE')}`",
            f"- lensing: `{best.get('chi2_lensing')}`",
            "",
        ]
    )


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    headers = ["c_visibility_memory", "chi2_CMB", "chi2_highl", "chi2_lowl_EE", "chi2_lensing", "returncode"]
    CSV_PATH.write_text(
        "\n".join([",".join(headers)] + [",".join(str(row.get(h, "")) for h in headers) for row in payload["rows"]]) + "\n",
        encoding="utf-8",
    )
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
