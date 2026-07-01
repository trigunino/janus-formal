from __future__ import annotations

from pathlib import Path
import json

try:
    from scripts.build_p0_eft_delta_neff_residual_closure import build_payload as residual_payload
    from scripts.build_p0_eft_janus_holst_distance_ruler_map import master_branch_background
except ModuleNotFoundError:
    from build_p0_eft_delta_neff_residual_closure import build_payload as residual_payload
    from build_p0_eft_janus_holst_distance_ruler_map import master_branch_background


REPORT_PATH = Path("outputs/reports/p0_eft_residual_factor_geometric_origin.md")
JSON_PATH = Path("outputs/reports/p0_eft_residual_factor_geometric_origin.json")


def origin_candidates() -> list[dict]:
    return [
        {"name": "pin_minus_dirac_4_times_orbifold_2_times_boundary_6", "denominator": 4 * 2 * 6},
        {"name": "holst_eta2_times_dirac_4_times_orbifold_2_plus_boundary_18", "denominator": 2 * 4 * 2 + 18},
        {"name": "clifford_trace_4_times_aps_5d_boundary_5_times_pin_2", "denominator": 4 * 5 * 2},
        {"name": "dirac_4_times_orbifold_2_times_sigma_codim_5", "denominator": 4 * 2 * 5},
        {"name": "empirical_target_50", "denominator": 50},
    ]


def build_payload() -> dict:
    residual = residual_payload()
    constants, _ = master_branch_background()
    a_sigma = float(constants["a_sigma"])
    exact_fraction = float(residual["exact_required_fractional_correction"])
    rows = []
    for candidate in origin_candidates():
        value = (1.0 - a_sigma) / candidate["denominator"]
        rows.append(
            {
                **candidate,
                "fractional_correction": value,
                "target_fractional_correction": exact_fraction,
                "abs_residual": abs(value - exact_fraction),
                "relative_residual": abs(value - exact_fraction) / exact_fraction,
            }
        )
    best = min(rows, key=lambda row: row["abs_residual"])
    return {
        "description": "Geometric-origin scan for the residual factor multiplying the Holst plasma Delta N_eff candidate.",
        "status": "residual-factor-geometric-origin-scored",
        "a_sigma": a_sigma,
        "target_fractional_correction": exact_fraction,
        "candidates": rows,
        "best_candidate": best,
        "best_is_non_empirical": best["name"] != "empirical_target_50",
        "is_derived_geometry": False,
        "next_required": "derive denominator 50 from an actual Holst/Pin/orbifold degree-of-freedom trace, not from candidate numerology.",
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Residual Factor Geometric Origin",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Derived geometry: {payload['is_derived_geometry']}",
        f"Best is non-empirical: {payload['best_is_non_empirical']}",
        "",
        "## Candidates",
        "",
        "| name | denominator | correction | relative residual |",
        "|---|---:|---:|---:|",
    ]
    for row in sorted(payload["candidates"], key=lambda item: item["abs_residual"]):
        lines.append(
            f"| {row['name']} | {row['denominator']} | "
            f"{row['fractional_correction']:.6g} | {row['relative_residual']:.6g} |"
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
