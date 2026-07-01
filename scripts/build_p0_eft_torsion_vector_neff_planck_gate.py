from __future__ import annotations

from pathlib import Path
import json
import os
import re
import subprocess
import sys

try:
    from scripts.build_p0_eft_sound_horizon_global_integral import build_payload as sound_global
except ModuleNotFoundError:
    from build_p0_eft_sound_horizon_global_integral import build_payload as sound_global


REPORT_PATH = Path("outputs/reports/p0_eft_torsion_vector_neff_planck_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_torsion_vector_neff_planck_gate.json")
YAML_PATH = Path("outputs/cmb_bridge/cobaya_planck_torsion_vector_neff_gate.yaml")
FORK_PATH = Path("external/camb_janus_fork").resolve()
PACKAGES_PATH = Path("external/cobaya_packages")


def winget_gfortran_bin() -> str | None:
    root = Path(os.environ.get("LOCALAPPDATA", "")) / "Microsoft/WinGet/Packages"
    matches = list(root.rglob("gfortran.exe")) if root.exists() else []
    return str(matches[0].parent) if matches else None


def write_yaml(nnu: float) -> None:
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
  H0: 67.4
  ombh2: 0.02237
  omch2: 0.136
  tau: 0.054
  As: 2.1e-9
  ns: 0.965
  mnu: 0.06
  nnu: {nnu}
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


def run_point(nnu: float) -> dict:
    write_yaml(nnu)
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
        "nnu": nnu,
        "returncode": result.returncode,
        "chi2_highl": parse(output, "planck_2018_highl_plik.TTTEEE"),
        "chi2_lowl_TT": parse(output, "planck_2018_lowl.TT"),
        "chi2_lowl_EE": parse(output, "planck_2018_lowl.EE"),
        "chi2_lensing": parse(output, "planck_2018_lensing.clik"),
        "chi2_CMB": float(total_match.group(1)) if total_match else None,
    }


def build_payload() -> dict:
    sound = sound_global()
    current_nnu = float(sound["neff_janus"])
    required_nnu = float(sound["neff_ref"]) + float(sound["required_delta_neff_for_bao_ratio"])
    packages_ready = PACKAGES_PATH.exists()
    fork_ready = (FORK_PATH / "camb/cambdll.dll").exists()
    rows = [run_point(current_nnu), run_point(required_nnu)] if packages_ready and fork_ready else []
    valid = [row for row in rows if row["returncode"] == 0 and row["chi2_CMB"] is not None]
    best = min(valid, key=lambda row: row["chi2_CMB"]) if valid else None
    return {
        "description": "Direct Planck gate for Route A: torsion-vector radiation represented as extra N_eff.",
        "status": "torsion-vector-neff-planck-gate-run",
        "packages_ready": packages_ready,
        "fork_ready": fork_ready,
        "current_nnu": current_nnu,
        "required_nnu_for_bao_rd": required_nnu,
        "rows": rows,
        "best": best,
        "route_a_improves_planck": bool(
            len(valid) == 2 and valid[1]["chi2_CMB"] < valid[0]["chi2_CMB"]
        ),
        "route_a_planck_accepted": bool(best and best["chi2_CMB"] < 2000.0),
        "is_derived_geometry": False,
        "next_required": "If required N_eff worsens Planck, Route A cannot be a simple free-radiation carrier; test Immirzi G_eff or refit early parameters jointly.",
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Torsion Vector Neff Planck Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Route A improves Planck: {payload['route_a_improves_planck']}",
        f"Route A accepted: {payload['route_a_planck_accepted']}",
        f"Derived geometry: {payload['is_derived_geometry']}",
        "",
        "| case | nnu | chi2 CMB | highl | lowE |",
        "|---|---:|---:|---:|---:|",
    ]
    for row in payload["rows"]:
        name = "required_rd" if abs(row["nnu"] - payload["required_nnu_for_bao_rd"]) < 1e-6 else "current"
        lines.append(
            f"| {name} | {row['nnu']:.6g} | {row.get('chi2_CMB')} | "
            f"{row.get('chi2_highl')} | {row.get('chi2_lowl_EE')} |"
        )
    lines.extend(["", "## Next", "", payload["next_required"], ""])
    return "\n".join(lines)


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
