from __future__ import annotations

from pathlib import Path
import json
import os
import re
import subprocess
import sys


REPORT_PATH = Path("outputs/reports/p0_eft_immirzi_patch_mini_scan.md")
JSON_PATH = Path("outputs/reports/p0_eft_immirzi_patch_mini_scan.json")
CSV_PATH = Path("outputs/reports/p0_eft_immirzi_patch_mini_scan.csv")
YAML_PATH = Path("outputs/cmb_bridge/cobaya_planck_immirzi_patch_mini_scan.yaml")
FORK_PATH = Path("external/camb_janus_fork").resolve()
SOURCE_PATH = Path("external/camb_janus_fork/fortran/JanusHolstSources.f90")


def winget_gfortran_bin() -> str | None:
    root = Path(os.environ.get("LOCALAPPDATA", "")) / "Microsoft/WinGet/Packages"
    matches = list(root.rglob("gfortran.exe")) if root.exists() else []
    return str(matches[0].parent) if matches else None


def replace_param(text: str, param_name: str, value: float, count: int = 0) -> str:
    pattern = rf"(real\(dl\), parameter :: {re.escape(param_name)} = )[-+0-9.eE]+_dl"
    return re.sub(pattern, rf"\g<1>{value:.16e}_dl", text, count=count)


def set_immirzi_params(delta_i: float, width: float) -> None:
    text = SOURCE_PATH.read_text(encoding="utf-8")
    text = replace_param(text, "width", width, count=1)
    text = replace_param(text, "c_geff", delta_i)
    text = replace_param(text, "c_immirzi", delta_i)
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


def grid() -> list[dict[str, float]]:
    return [
        {"delta_i": delta_i, "width": width}
        for delta_i in [0.03, 0.06, 0.09778424139658529, 0.13]
        for width in [1.0e-4, 2.0e-4, 4.0e-4]
    ]


def run_point(point: dict[str, float]) -> dict:
    set_immirzi_params(point["delta_i"], point["width"])
    build_code = build_fork()
    result = run_cobaya() if build_code == 0 else {"returncode": build_code, "chi2_CMB": None}
    return {**point, "build_returncode": build_code, **result}


def build_payload(points: list[dict[str, float]] | None = None, execute: bool = True) -> dict:
    points = points or grid()
    original = SOURCE_PATH.read_text(encoding="utf-8")
    rows: list[dict] = []
    try:
        if execute:
            rows = [run_point(point) for point in points]
        else:
            rows = [{**point, "build_returncode": None, "chi2_CMB": None} for point in points]
    finally:
        SOURCE_PATH.write_text(original, encoding="utf-8")
        build_fork()
    valid = [row for row in rows if row.get("returncode") == 0 and row.get("chi2_CMB") is not None]
    best = min(valid, key=lambda row: row["chi2_CMB"]) if valid else None
    accepted = bool(best and best["chi2_CMB"] < 2000.0)
    return {
        "description": "Mini-scan of active coherent Immirzi CAMB patch against Planck.",
        "status": "immirzi-patch-mini-scan-run" if execute else "immirzi-patch-mini-scan-dry",
        "grid_size": len(points),
        "valid_points": len(valid),
        "rows": rows,
        "best": best,
        "planck_accepted": accepted,
        "full_cosmology_prediction_ready_no_fit": False,
        "next_required": "If no point is accepted, freeze CMB branch as excluded or derive additional lowE/reionization physics.",
    }


def render_markdown(payload: dict) -> str:
    best = payload["best"] or {}
    lines = [
        "# P0 EFT Immirzi Patch Mini Scan",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Grid size: {payload['grid_size']}",
        f"Valid points: {payload['valid_points']}",
        f"Planck accepted: {payload['planck_accepted']}",
        "",
        "## Best",
        "",
        f"- delta_i: `{best.get('delta_i')}`",
        f"- width: `{best.get('width')}`",
        f"- chi2 CMB: `{best.get('chi2_CMB')}`",
        f"- highl: `{best.get('chi2_highl')}`",
        f"- lowE: `{best.get('chi2_lowl_EE')}`",
        f"- lensing: `{best.get('chi2_lensing')}`",
        "",
        "## Next",
        "",
        payload["next_required"],
        "",
    ]
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    headers = ["delta_i", "width", "chi2_CMB", "chi2_highl", "chi2_lowl_EE", "chi2_lensing", "returncode"]
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
