from __future__ import annotations

from pathlib import Path
import json
import os
import re
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.run_p0_eft_coherent_primordial_immirzi_planck_gate import (
    FORK_PATH,
    SOURCE_PATH,
    delta_i,
    set_coherent_immirzi,
    build_fork,
    winget_gfortran_bin,
)


REPORT_PATH = Path("outputs/reports/p0_eft_coherent_immirzi_planck_channel_delta.md")
JSON_PATH = Path("outputs/reports/p0_eft_coherent_immirzi_planck_channel_delta.json")
CSV_PATH = Path("outputs/reports/p0_eft_coherent_immirzi_planck_channel_delta.csv")
YAML_PATH = Path("outputs/cmb_bridge/cobaya_planck_coherent_channel_delta.yaml")

REFERENCE = {
    "H0": 67.36,
    "ombh2": 0.02237,
    "omch2": 0.12,
    "tau": 0.0544,
    "As": 2.1e-9,
    "ns": 0.9649,
    "nnu": 3.044,
}
JANUS = {
    "H0": 67.4,
    "ombh2": 0.02237,
    "omch2": 0.136,
    "tau": 0.054,
    "As": 2.1e-9,
    "ns": 0.965,
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


def write_yaml(component: str, params: dict[str, float]) -> None:
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


def parse(output: str, component: str) -> float | None:
    match = re.search(rf"chi2_{re.escape(component)}\s*=\s*([0-9.eE+-]+)", output)
    return float(match.group(1)) if match else None


def run_channel(component: str, params: dict[str, float]) -> dict:
    write_yaml(component, params)
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
    return {"returncode": result.returncode, "chi2": parse(result.stdout + result.stderr, component)}


def build_payload(execute: bool = True) -> dict:
    value = delta_i()
    if not execute:
        return {
            "description": "Per-channel raw Planck delta diagnostic for coherent Immirzi stress tensor.",
            "status": "coherent-immirzi-channel-delta-dry",
            "c_coherent_immirzi": value,
            "rows": [],
            "full_cosmology_prediction_ready_no_fit": False,
        }
    original = SOURCE_PATH.read_text(encoding="utf-8")
    rows = []
    try:
        set_coherent_immirzi(0.0)
        build_fork()
        refs = {name: run_channel(component, REFERENCE) for name, component in CHANNELS.items()}
        set_coherent_immirzi(value)
        build_fork()
        for name, component in CHANNELS.items():
            janus = run_channel(component, JANUS)
            ref = refs[name]
            delta = janus["chi2"] - ref["chi2"] if janus["chi2"] is not None and ref["chi2"] is not None else None
            rows.append(
                {
                    "channel": name,
                    "component": component,
                    "reference_chi2": ref["chi2"],
                    "janus_chi2": janus["chi2"],
                    "delta_chi2": delta,
                    "returncode": janus["returncode"],
                }
            )
    finally:
        SOURCE_PATH.write_text(original, encoding="utf-8")
        build_fork()
    worst = max([row for row in rows if row["delta_chi2"] is not None], key=lambda row: row["delta_chi2"])
    return {
        "description": "Per-channel raw Planck delta diagnostic for coherent Immirzi stress tensor.",
        "status": "coherent-immirzi-channel-delta-run",
        "c_coherent_immirzi": value,
        "rows": rows,
        "worst_delta_channel": worst,
        "highl_delta_sum": sum(row["delta_chi2"] for row in rows if row["channel"].startswith("highl_") and row["delta_chi2"] is not None),
        "full_cosmology_prediction_ready_no_fit": False,
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Coherent Immirzi Planck Channel Delta",
        "",
        payload["description"],
        "",
        f"Status: `{payload['status']}`",
        f"Worst channel: `{payload.get('worst_delta_channel', {}).get('channel')}`",
        f"High-l delta sum: `{payload.get('highl_delta_sum')}`",
        "",
        "| channel | reference chi2 | Janus chi2 | delta |",
        "|---|---:|---:|---:|",
    ]
    for row in payload["rows"]:
        lines.append(f"| {row['channel']} | {row['reference_chi2']} | {row['janus_chi2']} | {row['delta_chi2']} |")
    return "\n".join(lines) + "\n"


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH, execute: bool = True) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload(execute=execute)
    headers = ["channel", "component", "reference_chi2", "janus_chi2", "delta_chi2", "returncode"]
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
