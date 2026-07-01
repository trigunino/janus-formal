from __future__ import annotations

from pathlib import Path
import json

import numpy as np

try:
    from scripts.build_kids1000_cosebis_contract import build_cosebis_contract
    from scripts.build_kids1000_janus_holst_shape_chi2 import best_amplitude, slice_contract
    from scripts.build_kids1000_janus_holst_weyl_cosebis import build_payload as build_holst_payload
except ModuleNotFoundError:
    from build_kids1000_cosebis_contract import build_cosebis_contract
    from build_kids1000_janus_holst_shape_chi2 import best_amplitude, slice_contract
    from build_kids1000_janus_holst_weyl_cosebis import build_payload as build_holst_payload


REPORT_PATH = Path("outputs/reports/kids1000_janus_holst_mode_cut_audit.md")
JSON_PATH = Path("outputs/reports/kids1000_janus_holst_mode_cut_audit.json")


def contract_indices_for_modes(kept_modes: int, *, total_modes_per_pair: int = 20, pair_count: int = 15) -> list[int]:
    return [
        pair_index * total_modes_per_pair + mode_index
        for pair_index in range(pair_count)
        for mode_index in range(kept_modes)
    ]


def holst_indices_for_modes(kept_modes: int, *, holst_modes_per_pair: int = 5, pair_count: int = 15) -> list[int]:
    return [
        pair_index * holst_modes_per_pair + mode_index
        for pair_index in range(pair_count)
        for mode_index in range(kept_modes)
    ]


def build_payload() -> dict:
    contract = build_cosebis_contract()
    holst = build_holst_payload()
    rows = []
    for kept_modes in range(1, 6):
        observed, covariance = slice_contract(contract, contract_indices_for_modes(kept_modes))
        shape = np.asarray(
            [
                holst["rows"][index]["janus_holst_cosebis_en"]
                for index in holst_indices_for_modes(kept_modes)
            ],
            dtype=float,
        )
        amplitude, chi2 = best_amplitude(observed, shape, covariance)
        rows.append(
            {
                "kept_modes_per_pair": kept_modes,
                "dimension": int(observed.size),
                "best_amplitude": amplitude,
                "chi2": chi2,
                "dof": int(observed.size - 1),
                "chi2_per_dof": chi2 / (observed.size - 1),
            }
        )
    return {
        "description": "COSEBIs mode-cut audit for the KiDS-1000 Janus-Holst shape.",
        "status": "diagnostic-mode-cut-audit-computed",
        "rows": rows,
        "prediction_ready": False,
        "boundary": (
            "This scans already-inspected KiDS modes and is therefore diagnostic only. A final "
            "scale cut must be fixed by a source-derived nonlinear/baryon policy."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# KiDS-1000 Janus-Holst Mode-Cut Audit",
        "",
        payload["description"],
        "",
        f"Status: `{payload['status']}`",
        f"Prediction ready: `{payload['prediction_ready']}`",
        "",
        "| kept modes/pair | dimension | best amplitude | chi2 | dof | chi2/dof |",
        "|---:|---:|---:|---:|---:|---:|",
    ]
    for row in payload["rows"]:
        lines.append(
            f"| {row['kept_modes_per_pair']} | {row['dimension']} | {row['best_amplitude']:.6g} | "
            f"{row['chi2']:.6g} | {row['dof']} | {row['chi2_per_dof']:.6g} |"
        )
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
