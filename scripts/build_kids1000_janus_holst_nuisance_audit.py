from __future__ import annotations

from pathlib import Path
import json

import numpy as np

try:
    from scripts.build_kids1000_cosebis_contract import build_cosebis_contract
    from scripts.build_kids1000_janus_holst_shape_chi2 import (
        pair_chi2_blocks,
        scale_cut_indices,
        slice_contract,
    )
    from scripts.build_kids1000_janus_holst_weyl_cosebis import build_payload as build_holst_payload
except ModuleNotFoundError:
    from build_kids1000_cosebis_contract import build_cosebis_contract
    from build_kids1000_janus_holst_shape_chi2 import pair_chi2_blocks, scale_cut_indices, slice_contract
    from build_kids1000_janus_holst_weyl_cosebis import build_payload as build_holst_payload

from janus_lab.statistics import weighted_linear_fit


REPORT_PATH = Path("outputs/reports/kids1000_janus_holst_nuisance_audit.md")
JSON_PATH = Path("outputs/reports/kids1000_janus_holst_nuisance_audit.json")


def centered(values: np.ndarray) -> np.ndarray:
    arr = np.asarray(values, dtype=float)
    return arr - float(np.mean(arr))


def nuisance_design(rows: list[dict], shape: np.ndarray) -> tuple[list[str], np.ndarray]:
    pair_mean_bin = np.asarray([(row["bin1"] + row["bin2"]) / 2.0 for row in rows], dtype=float)
    mode = np.asarray([row["angbin"] for row in rows], dtype=float)
    labels = ["amplitude", "pair_bin_tilt", "mode_tilt"]
    design = np.column_stack(
        [
            shape,
            shape * centered(pair_mean_bin),
            shape * centered(mode),
        ]
    )
    return labels, design


def fit_model(
    name: str,
    labels: list[str],
    design: np.ndarray,
    observed: np.ndarray,
    covariance: np.ndarray,
    rows: list[dict],
) -> dict:
    coeffs, prediction, chi2 = weighted_linear_fit(design, observed, covariance)
    n_params = int(design.shape[1])
    residuals = prediction - observed
    return {
        "name": name,
        "n_params": n_params,
        "coefficients": {label: float(value) for label, value in zip(labels, coeffs)},
        "chi2": float(chi2),
        "dof": int(observed.size - n_params),
        "chi2_per_dof": float(chi2 / (observed.size - n_params)),
        "aic": float(chi2 + 2.0 * n_params),
        "bic": float(chi2 + n_params * np.log(observed.size)),
        "pair_chi2_blocks": pair_chi2_blocks(
            [{"bin1": row["bin1"], "bin2": row["bin2"], "angbin": row["angbin"]} for row in rows],
            residuals,
            covariance,
        ),
    }


def build_payload() -> dict:
    contract = build_cosebis_contract()
    holst = build_holst_payload()
    indices = scale_cut_indices()
    observed, covariance = slice_contract(contract, indices)
    rows = holst["rows"]
    shape = np.asarray([row["janus_holst_cosebis_en"] for row in rows], dtype=float)
    labels, design = nuisance_design(rows, shape)
    models = [
        fit_model("amplitude_only", labels[:1], design[:, :1], observed, covariance, rows),
        fit_model("amplitude_plus_pair_bin_tilt", labels[:2], design[:, :2], observed, covariance, rows),
        fit_model("amplitude_plus_mode_tilt", [labels[0], labels[2]], design[:, [0, 2]], observed, covariance, rows),
        fit_model("amplitude_plus_pair_bin_and_mode_tilt", labels, design, observed, covariance, rows),
    ]
    best_by_aic = min(models, key=lambda item: item["aic"])
    return {
        "description": "Diagnostic nuisance audit for the KiDS-1000 Janus-Holst COSEBIs shape.",
        "status": "diagnostic-nuisance-audit-computed",
        "dimension": int(observed.size),
        "templates": labels,
        "models": models,
        "best_by_aic": best_by_aic["name"],
        "prediction_ready": False,
        "chi2_claim_ready": False,
        "boundary": (
            "These pair-bin and mode tilts are diagnostic templates only. They are not an IA "
            "or baryon closure and must not be used to claim a Janus prediction."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# KiDS-1000 Janus-Holst Nuisance Audit",
        "",
        payload["description"],
        "",
        f"Status: `{payload['status']}`",
        f"Dimension: `{payload['dimension']}`",
        f"Prediction ready: `{payload['prediction_ready']}`",
        f"Best by AIC: `{payload['best_by_aic']}`",
        "",
        "| model | n params | chi2 | dof | chi2/dof | AIC | BIC |",
        "|---|---:|---:|---:|---:|---:|---:|",
    ]
    for model in payload["models"]:
        lines.append(
            f"| {model['name']} | {model['n_params']} | {model['chi2']:.6g} | "
            f"{model['dof']} | {model['chi2_per_dof']:.6g} | {model['aic']:.6g} | {model['bic']:.6g} |"
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
