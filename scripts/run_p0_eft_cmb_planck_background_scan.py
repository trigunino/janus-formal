from __future__ import annotations

from pathlib import Path
import itertools
import json
import os
import re
import subprocess
import sys

REPORT_PATH = Path("outputs/reports/p0_eft_cmb_planck_background_scan.md")
JSON_PATH = Path("outputs/reports/p0_eft_cmb_planck_background_scan.json")
CSV_PATH = Path("outputs/reports/p0_eft_cmb_planck_background_scan.csv")
YAML_PATH = Path("outputs/cmb_bridge/cobaya_planck_full_janus_background_scan.yaml")
FORK_PATH = Path("external/camb_janus_fork").resolve()


def winget_gfortran_bin() -> str | None:
    root = Path(os.environ.get("LOCALAPPDATA", "")) / "Microsoft/WinGet/Packages"
    matches = list(root.rglob("gfortran.exe")) if root.exists() else []
    return str(matches[0].parent) if matches else None


def write_yaml(p: dict[str, float]) -> None:
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
  H0: {p["H0"]}
  ombh2: {p["ombh2"]}
  omch2: {p["omch2"]}
  tau: {p["tau"]}
  As: {p["As"]}
  ns: {p["ns"]}
  mnu: 0.06
  nnu: {p["nnu"]}
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


def run_point(p: dict[str, float]) -> dict:
    write_yaml(p)
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
        **p,
        "returncode": result.returncode,
        "chi2_highl": parse(output, "planck_2018_highl_plik.TTTEEE"),
        "chi2_lowl_TT": parse(output, "planck_2018_lowl.TT"),
        "chi2_lowl_EE": parse(output, "planck_2018_lowl.EE"),
        "chi2_lensing": parse(output, "planck_2018_lensing.clik"),
        "chi2_CMB": float(total_match.group(1)) if total_match else None,
    }


def grid() -> list[dict[str, float]]:
    return [
        {
            "H0": H0,
            "ombh2": ombh2,
            "omch2": omch2,
            "As": As,
            "ns": ns,
            "tau": tau,
            "nnu": nnu,
        }
        for H0, ombh2, omch2, As, ns, tau, nnu in itertools.product(
            [62.0, 67.4],
            [0.0215, 0.0224],
            [0.11, 0.136],
            [1.8e-9, 2.1e-9],
            [0.94, 0.97],
            [0.035, 0.055],
            [3.046, 3.7424238],
        )
    ]


def build_payload(limit: int | None = None) -> dict:
    points = grid()[:limit]
    rows = [run_point(point) for point in points]
    valid = [row for row in rows if row["returncode"] == 0 and row["chi2_CMB"] is not None]
    best = min(valid, key=lambda row: row["chi2_CMB"]) if valid else None
    headers = [
        "H0",
        "ombh2",
        "omch2",
        "As",
        "ns",
        "tau",
        "nnu",
        "chi2_CMB",
        "chi2_highl",
        "chi2_lowl_TT",
        "chi2_lowl_EE",
        "chi2_lensing",
        "returncode",
    ]
    CSV_PATH.parent.mkdir(parents=True, exist_ok=True)
    CSV_PATH.write_text(
        "\n".join([",".join(headers)] + [",".join(str(row.get(h, "")) for h in headers) for row in rows]) + "\n",
        encoding="utf-8",
    )
    return {
        "description": "Coarse direct Planck background scan using the compiled Janus-patched CAMB fork.",
        "status": "planck-background-scan-run",
        "grid_size": len(points),
        "valid_points": len(valid),
        "best": best,
        "csv": str(CSV_PATH),
        "cmb_accepted_threshold": 2000.0,
        "best_accepted": bool(best and best["chi2_CMB"] < 2000.0),
        "next_required": "If still rejected, the issue is not only late background parameters; inspect recombination/lowE/polarization sector.",
    }


def render_markdown(payload: dict) -> str:
    b = payload["best"] or {}
    return "\n".join(
        [
            "# P0 EFT CMB Planck Background Scan",
            "",
            payload["description"],
            "",
            f"Status: {payload['status']}",
            f"Grid size: {payload['grid_size']}",
            f"Valid points: {payload['valid_points']}",
            f"Best accepted: {payload['best_accepted']}",
            "",
            "## Best",
            "",
            f"- chi2_CMB: `{b.get('chi2_CMB')}`",
            f"- H0: `{b.get('H0')}`",
            f"- ombh2: `{b.get('ombh2')}`",
            f"- omch2: `{b.get('omch2')}`",
            f"- As: `{b.get('As')}`",
            f"- ns: `{b.get('ns')}`",
            f"- tau: `{b.get('tau')}`",
            f"- nnu: `{b.get('nnu')}`",
            f"- highl: `{b.get('chi2_highl')}`",
            f"- lowE: `{b.get('chi2_lowl_EE')}`",
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
