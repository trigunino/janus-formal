from __future__ import annotations

from pathlib import Path
from argparse import ArgumentParser
import json


RESOLUTION_PATH = Path("outputs/reports/pm_qcross_absolute_shear_resolution.json")
REPORT_PATH = Path("outputs/reports/pm_band_limited_shear_convergence.md")
JSON_PATH = Path("outputs/reports/pm_band_limited_shear_convergence.json")
MAX_RELATIVE_POWER_CHANGE = 1.0


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def parse_args():
    parser = ArgumentParser()
    parser.add_argument("--input-json", default=str(RESOLUTION_PATH))
    parser.add_argument("--output-tag", default="")
    return parser.parse_args()


def tagged_path(path: Path, tag: str) -> Path:
    if not tag:
        return path
    safe = tag.replace("-", "_")
    return path.with_name(f"{path.stem}_{safe}{path.suffix}")


def relative_change(previous: float, current: float) -> float | None:
    if previous == 0.0:
        return None if current == 0.0 else float("inf")
    return abs(current - previous) / abs(previous)


def build_payload(
    resolution: dict,
    *,
    max_relative_power_change: float = MAX_RELATIVE_POWER_CHANGE,
) -> dict:
    rows = resolution["rows"]
    if len(rows) < 2:
        raise ValueError("at least two grid rows are required.")
    common_band_count = min(len(row.get("shear_power_bands", [])) for row in rows)
    bands = []
    for index in range(common_band_count):
        row_bands = [row["shear_power_bands"][index] for row in rows]
        if any(int(band["mode_count"]) <= 0 for band in row_bands):
            continue
        powers = [float(band["power"]) for band in row_bands]
        changes = [
            relative_change(previous, current)
            for previous, current in zip(powers[:-1], powers[1:])
        ]
        finite_changes = [change for change in changes if change is not None]
        final_change = changes[-1]
        stable = (
            final_change is not None
            and final_change <= max_relative_power_change
        )
        bands.append(
            {
                "band_index": index,
                "k_center_inv_mpc": float(row_bands[-1]["k_center_inv_mpc"]),
                "powers": powers,
                "relative_changes": changes,
                "max_relative_change": max(finite_changes) if finite_changes else None,
                "final_relative_change": final_change,
                "stable": stable,
            }
        )
    stable_bands = [band for band in bands if band["stable"]]
    return {
        "description": "Band-limited convergence audit for PM Q_cross absolute shear.",
        "source_report": str(resolution.get("source_report", RESOLUTION_PATH)),
        "run_settings": resolution.get("run_settings", {}),
        "grids": resolution["grids"],
        "max_relative_power_change": max_relative_power_change,
        "common_band_count": len(bands),
        "stable_band_count": len(stable_bands),
        "bands": bands,
        "blocking_issue": len(stable_bands) == 0,
        "verdict": (
            "At least one fixed physical k-band is stable under the diagnostic threshold."
            if stable_bands
            else "No fixed physical k-band is stable; keep PM shear convergence blocked."
        ),
        "boundary": (
            "Diagnostic only. This compares fixed physical Fourier bands and does not "
            "replace Bianchi, Q_det, Q_cross, IC or survey derivations."
        ),
    }


def build_payload_from_file(path: Path = RESOLUTION_PATH) -> dict:
    resolution = load_json(path)
    resolution["source_report"] = str(path)
    return build_payload(resolution)


def render_markdown(payload: dict) -> str:
    lines = [
        "# PM Band-Limited Shear Convergence",
        "",
        payload["description"],
        "",
        f"- grids: {payload['grids']}",
        f"- max relative power change: {payload['max_relative_power_change']}",
        f"- stable bands: {payload['stable_band_count']} / {payload['common_band_count']}",
        "",
        "| band | k center [1/Mpc] | final relative change | stable |",
        "|---:|---:|---:|---|",
    ]
    for band in payload["bands"]:
        change = band["final_relative_change"]
        change_text = "" if change is None else f"{change:.6g}"
        lines.append(
            f"| {band['band_index']} | {band['k_center_inv_mpc']:.9g} | "
            f"{change_text} | {band['stable']} |"
        )
    lines.extend(["", payload["boundary"], "", f"Verdict: {payload['verdict']}", ""])
    return "\n".join(lines)


def main() -> None:
    args = parse_args()
    report_path = tagged_path(REPORT_PATH, args.output_tag)
    json_path = tagged_path(JSON_PATH, args.output_tag)
    report_path.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload_from_file(Path(args.input_json))
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_text = render_markdown(payload)
    report_path.write_text(report_text, encoding="utf-8")
    print(f"Wrote {report_path}")
    print(f"Wrote {json_path}")


if __name__ == "__main__":
    main()
