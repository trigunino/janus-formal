from __future__ import annotations

from pathlib import Path
import csv
import json
import math

import numpy as np

try:
    from scripts.build_kids1000_cosebis_contract import (
        cosebis_fits_bytes,
        find_hdu,
        read_binary_table,
        read_fits_hdus,
    )
except ModuleNotFoundError:
    from build_kids1000_cosebis_contract import (
        cosebis_fits_bytes,
        find_hdu,
        read_binary_table,
        read_fits_hdus,
    )

from janus_lab.lensing import janus_source_distribution_lensing_kernel
from janus_lab.models import JanusExpansion


REPORT_PATH = Path("outputs/reports/kids1000_janus_cosebis_proxy_vector.md")
JSON_PATH = Path("outputs/reports/kids1000_janus_cosebis_proxy_vector.json")
CSV_PATH = Path("outputs/reports/kids1000_janus_cosebis_proxy_vector.csv")


def extract_cosebis_rows(data: bytes | None = None) -> tuple[list[dict], list[dict]]:
    fits = data if data is not None else cosebis_fits_bytes()
    hdus = read_fits_hdus(fits)
    return read_binary_table(fits, find_hdu(hdus, "En")), read_binary_table(
        fits,
        find_hdu(hdus, "NZ_SOURCE"),
    )


def source_distribution(nz_rows: list[dict], bin_index: int) -> tuple[np.ndarray, np.ndarray]:
    z = np.asarray([float(row["Z_MID"]) for row in nz_rows], dtype=float)
    weights = np.asarray([float(row[f"BIN{bin_index}"]) for row in nz_rows], dtype=float)
    mask = (z > 0.0) & (weights > 0.0)
    if not np.any(mask):
        raise ValueError(f"empty source distribution for BIN{bin_index}")
    z = z[mask]
    weights = weights[mask]
    return z, weights / float(np.sum(weights))


def bin_kernel_scores(
    nz_rows: list[dict],
    *,
    model: JanusExpansion,
    lens_grid_size: int = 256,
    bin_count: int = 5,
) -> dict[int, float]:
    z_max = max(float(row["Z_MID"]) for row in nz_rows)
    z_lens = np.linspace(0.0, min(z_max, model.z_max), lens_grid_size)
    scores: dict[int, float] = {}
    for bin_index in range(1, bin_count + 1):
        source_z, source_weights = source_distribution(nz_rows, bin_index)
        source_mask = source_z <= model.z_max
        if not np.any(source_mask):
            raise ValueError(f"source distribution for BIN{bin_index} exceeds Janus z_max")
        kernel = np.asarray(
            janus_source_distribution_lensing_kernel(
                z_lens,
                source_z[source_mask],
                source_weights[source_mask],
                model,
            ),
            dtype=float,
        )
        scores[bin_index] = float(np.trapezoid(kernel, z_lens))
    return scores


def cosebis_proxy_shape(
    en_rows: list[dict],
    nz_rows: list[dict],
    *,
    q0: float = -0.087,
    mode_power: float = 2.0,
) -> list[dict[str, float | int]]:
    model = JanusExpansion.from_q0(q0)
    bin_count = max(max(int(row["BIN1"]), int(row["BIN2"])) for row in en_rows)
    scores = bin_kernel_scores(nz_rows, model=model, bin_count=bin_count)
    raw_values = []
    for row in en_rows:
        bin1 = int(row["BIN1"])
        bin2 = int(row["BIN2"])
        mode = int(row["ANGBIN"])
        pair_score = math.sqrt(scores[bin1] * scores[bin2])
        mode_weight = 1.0 / (float(mode) ** mode_power)
        raw_values.append(pair_score * mode_weight)
    scale = max(abs(value) for value in raw_values) or 1.0
    result = []
    for row, raw in zip(en_rows, raw_values):
        result.append(
            {
                "bin1": int(row["BIN1"]),
                "bin2": int(row["BIN2"]),
                "angbin": int(row["ANGBIN"]),
                "angle_arcmin": float(row["ANG"]),
                "janus_proxy_en_unit_shape": raw / scale,
            }
        )
    return result


def build_payload(data: bytes | None = None) -> dict:
    en_rows, nz_rows = extract_cosebis_rows(data)
    rows = cosebis_proxy_shape(en_rows, nz_rows)
    vector = [float(row["janus_proxy_en_unit_shape"]) for row in rows]
    return {
        "description": "Janus COSEBIs-order proxy vector for KiDS-1000 En.",
        "status": "janus-cosebis-order-proxy-vector-ready",
        "prediction_vector_id": "janus-kids1000-cosebis-proxy-unit-shape-v1",
        "dimension": len(vector),
        "same_order_as_kids_en": True,
        "n_fit_parameters": 0,
        "fit_to_kids_data": False,
        "prediction_ready": False,
        "vector": vector,
        "rows": rows,
        "boundary": (
            "Same-order diagnostic vector only. It uses Janus open-distance source-bin "
            "kernel scores and a fixed 1/n^2 mode damping; it is not a physical COSEBIs "
            "prediction. Use janus_lab.cosebis with physical Janus xi_+/xi_- curves for "
            "the COSEBIs/KCAP-equivalent path."
        ),
    }


def write_csv(rows: list[dict[str, float | int]], path: Path = CSV_PATH) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def render_markdown(payload: dict) -> str:
    lines = [
        "# KiDS-1000 Janus COSEBIs Proxy Vector",
        "",
        payload["description"],
        "",
        f"Status: `{payload['status']}`",
        f"Prediction vector id: `{payload['prediction_vector_id']}`",
        f"Dimension: `{payload['dimension']}`",
        f"Same order as KiDS En: `{payload['same_order_as_kids_en']}`",
        f"Prediction ready: `{payload['prediction_ready']}`",
        f"Fit to KiDS data: `{payload['fit_to_kids_data']}`",
        "",
        "| bin1 | bin2 | mode | angle arcmin | proxy En unit shape |",
        "|---:|---:|---:|---:|---:|",
    ]
    for row in payload["rows"][:20]:
        lines.append(
            f"| {row['bin1']} | {row['bin2']} | {row['angbin']} | "
            f"{row['angle_arcmin']:.6g} | {row['janus_proxy_en_unit_shape']:.6g} |"
        )
    lines.extend(["", payload["boundary"], ""])
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    write_csv(payload["rows"])
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")
    print(f"Wrote {CSV_PATH}")


if __name__ == "__main__":
    main()
