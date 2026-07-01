from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_janus_direct_cmb_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_direct_cmb_gate.json")


def build_payload() -> dict:
    observables = [
        {
            "name": "theta_star",
            "requires": ["Janus angular diameter distance to recombination", "Janus sound horizon/ruler map"],
            "ready": False,
        },
        {
            "name": "CMB_lensing_potential",
            "requires": ["Janus Weyl potential history", "Janus lensing kernel", "growth transfer functions"],
            "ready": False,
        },
        {
            "name": "primary_C_ell",
            "requires": ["Boltzmann hierarchy", "recombination visibility", "initial spectrum"],
            "ready": False,
        },
        {
            "name": "sigma8_direct",
            "requires": ["matter power transfer function", "normalization from primordial amplitude"],
            "ready": False,
        },
    ]
    return {
        "description": "Direct Janus CMB gate. This deliberately avoids LambdaCDM-derived compressed parameters.",
        "status": "janus-direct-cmb-observable-gate-open",
        "uses_lcdm_compressed_planck_parameters_as_verdict": False,
        "direct_cmb_likelihood_ready": False,
        "janus_holst_distance_ruler_map_ready": False,
        "observables": observables,
        "closed_inputs": [
            "Holst/membrane growth branch",
            "SDSS/eBOSS f_sigma8 full-covariance score",
            "DESI DR2 BAO data loader and covariance",
        ],
        "blocking_inputs": [
            "Janus/Holst H(z) background compatible with recombination",
            "Janus angular diameter distance D_A(z_star)",
            "Janus sound horizon or replacement ruler r_star",
            "Janus transfer functions for matter and Weyl potentials",
            "CMB likelihood wrapper or spectra emulator",
        ],
        "next_required": "derive P0EFTJanusHolstDistanceRulerMap before any Planck CMB verdict.",
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Janus Direct CMB Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Uses LCDM compressed Planck parameters as verdict: {payload['uses_lcdm_compressed_planck_parameters_as_verdict']}",
        f"Direct CMB likelihood ready: {payload['direct_cmb_likelihood_ready']}",
        f"Janus/Holst distance-ruler map ready: {payload['janus_holst_distance_ruler_map_ready']}",
        "",
        "## Observables",
        "",
        "| observable | ready | requires |",
        "|---|---:|---|",
    ]
    for row in payload["observables"]:
        lines.append(f"| {row['name']} | {row['ready']} | {', '.join(row['requires'])} |")
    lines.extend(["", "## Closed Inputs", ""])
    lines.extend(f"- {item}" for item in payload["closed_inputs"])
    lines.extend(["", "## Blocking Inputs", ""])
    lines.extend(f"- {item}" for item in payload["blocking_inputs"])
    lines.extend(["", f"Next: {payload['next_required']}", ""])
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
