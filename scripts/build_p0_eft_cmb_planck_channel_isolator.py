from __future__ import annotations

from pathlib import Path
import json
import os
import re
import subprocess
import sys

REPORT_PATH = Path("outputs/reports/p0_eft_cmb_planck_channel_isolator.md")
JSON_PATH = Path("outputs/reports/p0_eft_cmb_planck_channel_isolator.json")
CSV_PATH = Path("outputs/reports/p0_eft_cmb_planck_channel_isolator.csv")
YAML_PATH = Path("outputs/cmb_bridge/cobaya_planck_channel_isolator.yaml")
FORK_PATH = Path("external/camb_janus_fork").resolve()

BEST = {
    "H0": 67.4,
    "ombh2": 0.0224,
    "omch2": 0.136,
    "As": 2.1e-9,
    "ns": 0.94,
    "tau": 0.035,
    "nnu": 3.7424238,
}

CHANNELS = {
    "highl_TT": "planck_2018_highl_plik.TT",
    "highl_TE": "planck_2018_highl_plik.TE",
    "highl_EE": "planck_2018_highl_plik.EE",
    "lowl_TT": "planck_2018_lowl.TT",
    "lowl_EE": "planck_2018_lowl.EE",
    "lensing": "planck_2018_lensing.clik",
}


def winget_gfortran_bin() -> str | None:
    root = Path(os.environ.get("LOCALAPPDATA", "")) / "Microsoft/WinGet/Packages"
    matches = list(root.rglob("gfortran.exe")) if root.exists() else []
    return str(matches[0].parent) if matches else None


def write_yaml(component: str) -> None:
    YAML_PATH.parent.mkdir(parents=True, exist_ok=True)
    YAML_PATH.write_text(
        f"""\
output: null
theory:
  camb:
    extra_args:
      lens_potential_accuracy: 1
likelihood:
  {component}: null
params:
  H0: {BEST["H0"]}
  ombh2: {BEST["ombh2"]}
  omch2: {BEST["omch2"]}
  tau: {BEST["tau"]}
  As: {BEST["As"]}
  ns: {BEST["ns"]}
  mnu: 0.06
  nnu: {BEST["nnu"]}
  omk: 0
  YHe: 0.245
sampler:
  evaluate: null
packages_path: external/cobaya_packages
""",
        encoding="utf-8",
    )


def parse_chi2(output: str, component: str) -> float | None:
    match = re.search(rf"chi2_{re.escape(component)}\s*=\s*([0-9.eE+-]+)", output)
    return float(match.group(1)) if match else None


def run_channel(name: str, component: str) -> dict:
    write_yaml(component)
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
        "channel": name,
        "component": component,
        "returncode": result.returncode,
        "fork_camb_loaded": str(FORK_PATH).lower() in output.lower(),
        "chi2": parse_chi2(output, component),
    }


def build_payload() -> dict:
    rows = [run_channel(name, component) for name, component in CHANNELS.items()]
    valid = [row for row in rows if row["returncode"] == 0 and row["chi2"] is not None]
    unavailable = [row for row in rows if row["returncode"] != 0]
    worst = max(valid, key=lambda row: row["chi2"]) if valid else None
    CSV_PATH.parent.mkdir(parents=True, exist_ok=True)
    headers = ["channel", "component", "chi2", "returncode", "fork_camb_loaded"]
    CSV_PATH.write_text(
        "\n".join([",".join(headers)] + [",".join(str(row.get(h, "")) for h in headers) for row in rows]) + "\n",
        encoding="utf-8",
    )
    return {
        "description": "Planck channel isolator for the Janus CAMB fork at the current best CMB point.",
        "status": "planck-channel-isolator-run",
        "point": BEST,
        "channels": rows,
        "valid_channels": len(valid),
        "unavailable_channels": unavailable,
        "worst_channel": worst,
        "csv": str(CSV_PATH),
        "next_required": "Use the worst channel to decide whether to patch recombination/polarization or Weyl transfer shape.",
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT CMB Planck Channel Isolator",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
            f"Valid channels: {payload['valid_channels']}",
            f"Unavailable channels: `{[row['channel'] for row in payload['unavailable_channels']]}`",
        f"Worst channel: `{payload['worst_channel']['channel'] if payload['worst_channel'] else None}`",
        "",
        "## Channels",
        "",
    ]
    for row in payload["channels"]:
        lines.append(f"- {row['channel']}: chi2 `{row['chi2']}`")
    lines += ["", "## Next", "", payload["next_required"], ""]
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
    print(f"Wrote {CSV_PATH}")


if __name__ == "__main__":
    main()
