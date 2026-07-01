from __future__ import annotations

from pathlib import Path
import json

import numpy as np

try:
    from scripts.build_kids1000_cosebis_contract import build_cosebis_contract
except ModuleNotFoundError:
    from build_kids1000_cosebis_contract import build_cosebis_contract

from janus_lab.cosebis import evaluate_tplus, log_cosebis_filters


REPORT_PATH = Path("outputs/reports/kids1000_cosebis_operator.md")
JSON_PATH = Path("outputs/reports/kids1000_cosebis_operator.json")

THETA_MIN = 0.5
THETA_MAX = 300.0
N_MAX = 5
KEEP_ANG_EN = (0.5, 5.5)


def filter_diagnostics(samples: int = 50000) -> list[dict[str, float | int]]:
    filters = log_cosebis_filters(N_MAX, THETA_MIN, THETA_MAX)
    theta = np.geomspace(THETA_MIN, THETA_MAX, samples)
    rows = []
    for filter_ in filters:
        tplus = evaluate_tplus(filter_, theta)
        rows.append(
            {
                "mode": filter_.mode,
                "constraint_theta_tplus": float(np.trapezoid(theta * tplus, theta)),
                "constraint_theta3_tplus": float(np.trapezoid(theta**3 * tplus, theta)),
                "self_norm": float(np.trapezoid(theta * tplus * tplus, theta)),
            }
        )
    return rows


def selected_en_dimension(contract: dict) -> int:
    # KiDS scale_cuts keep_ang_En = 0.5 5.5, so modes 1..5 survive.
    return 15 * N_MAX


def build_payload() -> dict:
    contract = build_cosebis_contract()
    diagnostics = filter_diagnostics()
    return {
        "description": "KiDS-1000 COSEBIs operator surface matching the public KCAP settings.",
        "status": "cosebis-operator-ready",
        "theta_min_arcmin": THETA_MIN,
        "theta_max_arcmin": THETA_MAX,
        "n_max": N_MAX,
        "keep_ang_En": list(KEEP_ANG_EN),
        "full_en_dimension": len(contract["observed_vector"]),
        "scale_cut_en_dimension": selected_en_dimension(contract),
        "operator_formula": "E_n = 1/2 int_theta_min^theta_max dtheta theta [T_+n(theta) xi_+(theta) + T_-n(theta) xi_-(theta)]",
        "filter_diagnostics": diagnostics,
        "operator_ready": True,
        "janus_xi_prediction_ready": False,
        "chi2_ready": False,
        "next_required": [
            "derive or compute Janus xi_plus(theta) and xi_minus(theta) for each KiDS tomographic pair",
            "apply cosebis_vector_from_xi with the public KiDS En row order",
            "apply KiDS scale cuts before fixed_prediction_chi_square",
        ],
        "boundary": (
            "The COSEBIs transform is implemented. A KiDS chi-square remains blocked "
            "until Janus supplies physical xi_+/xi_- curves; the older same-order "
            "proxy vector is not a substitute for this operator."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# KiDS-1000 COSEBIs Operator",
        "",
        payload["description"],
        "",
        f"Status: `{payload['status']}`",
        f"Theta range: `{payload['theta_min_arcmin']}`-`{payload['theta_max_arcmin']}` arcmin",
        f"n_max: `{payload['n_max']}`",
        f"Full En dimension: `{payload['full_en_dimension']}`",
        f"Scale-cut En dimension: `{payload['scale_cut_en_dimension']}`",
        f"Operator ready: `{payload['operator_ready']}`",
        f"Janus xi prediction ready: `{payload['janus_xi_prediction_ready']}`",
        f"Chi2 ready: `{payload['chi2_ready']}`",
        "",
        "```text",
        payload["operator_formula"],
        "```",
        "",
        "| mode | int theta T+ | int theta^3 T+ | norm |",
        "|---:|---:|---:|---:|",
    ]
    for row in payload["filter_diagnostics"]:
        lines.append(
            f"| {row['mode']} | {row['constraint_theta_tplus']:.3g} | "
            f"{row['constraint_theta3_tplus']:.3g} | {row['self_norm']:.6g} |"
        )
    lines.extend(["", "## Next Required"])
    lines.extend(f"- {item}" for item in payload["next_required"])
    lines.extend(["", payload["boundary"], ""])
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
