from __future__ import annotations

from pathlib import Path
import json

import numpy as np

from janus_lab.field_statistics import rms
from janus_lab.lensing import positive_photon_weak_field_weyl_components_2d


REPORT_PATH = Path("outputs/reports/restricted_metric_weyl_chain.md")
JSON_PATH = Path("outputs/reports/restricted_metric_weyl_chain.json")


def gaussian_bump(grid: int, center: tuple[float, float], width: float) -> np.ndarray:
    axis = (np.arange(grid) + 0.5) / grid
    xx, yy = np.meshgrid(axis, axis, indexing="ij")
    radius2 = (xx - center[0]) ** 2 + (yy - center[1]) ** 2
    return np.exp(-0.5 * radius2 / width**2)


def summarize_case(name: str, positive: np.ndarray, negative: np.ndarray) -> dict:
    chain = positive_photon_weak_field_weyl_components_2d(
        positive,
        negative,
        box_size=1.0,
        source_provenance="source_derived",
        restricted_metric_closure=True,
    )
    center = tuple(index // 2 for index in positive.shape)
    return {
        "case": name,
        "restricted_metric_ready": bool(chain["restricted_metric_ready"]),
        "prediction_ready": bool(chain["prediction_ready"]),
        "center_convergence": float(chain["convergence"][center]),
        "gamma1_rms": rms(chain["gamma1"]),
        "gamma2_rms": rms(chain["gamma2"]),
        "weyl_trace_free_rms": rms(chain["weyl_trace_free_norm"]),
        "potential_min": float(np.min(chain["potential"])),
        "potential_max": float(np.max(chain["potential"])),
    }


def build_payload(grid: int = 64) -> dict:
    bump = gaussian_bump(grid, center=(0.5, 0.5), width=0.08)
    positive = np.ones((grid, grid), dtype=float)
    negative_cluster = np.ones((grid, grid), dtype=float) + bump
    negative_hole = np.maximum(np.ones((grid, grid), dtype=float) - 0.8 * bump, 0.0)
    rows = [
        summarize_case("negative_cluster", positive, negative_cluster),
        summarize_case("negative_hole", positive, negative_hole),
    ]
    return {
        "description": "Restricted comoving-scalar metric Weyl diagnostic.",
        "branch": "comoving scalar zero-Pi closure candidate",
        "grid": grid,
        "fit_used": False,
        "prediction_ready": False,
        "rows": rows,
        "boundary": (
            "restricted_metric_ready applies only to the comoving scalar zero-Pi branch; "
            "survey and tensor-lensing predictions remain blocked."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Restricted Metric Weyl Chain",
        "",
        payload["description"],
        "",
        f"Branch: {payload['branch']}",
        f"Fit used: {payload['fit_used']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| case | restricted metric ready | prediction ready | center convergence | gamma1 RMS | gamma2 RMS | Weyl TF RMS |",
        "|---|---|---|---:|---:|---:|---:|",
    ]
    for row in payload["rows"]:
        lines.append(
            f"| {row['case']} | {row['restricted_metric_ready']} | {row['prediction_ready']} | "
            f"{row['center_convergence']:.6g} | {row['gamma1_rms']:.6g} | "
            f"{row['gamma2_rms']:.6g} | {row['weyl_trace_free_rms']:.6g} |"
        )
    lines.extend(["", f"Boundary: {payload['boundary']}", ""])
    return "\n".join(lines)


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(render_markdown(payload), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
