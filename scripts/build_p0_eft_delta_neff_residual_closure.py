from __future__ import annotations

from pathlib import Path
import json
import math

try:
    from scripts.build_p0_eft_holst_plasma_delta_neff_derivation import build_payload as delta_payload
    from scripts.build_p0_eft_janus_holst_distance_ruler_map import master_branch_background
except ModuleNotFoundError:
    from build_p0_eft_holst_plasma_delta_neff_derivation import build_payload as delta_payload
    from build_p0_eft_janus_holst_distance_ruler_map import master_branch_background


REPORT_PATH = Path("outputs/reports/p0_eft_delta_neff_residual_closure.md")
JSON_PATH = Path("outputs/reports/p0_eft_delta_neff_residual_closure.json")


def correction_candidates(constants: dict, target: float, base: float) -> list[dict]:
    omega_m0 = float(constants["Omega_m0"])
    omega_t0 = float(constants["Omega_T0"])
    a_sigma = float(constants["a_sigma"])
    z_sigma = float(constants["z_sigma"])
    raw = [
        ("none", 1.0),
        ("one_plus_omega_t0_over_omega_m0", 1.0 + omega_t0 / omega_m0),
        ("one_plus_omega_t0", 1.0 + omega_t0),
        ("one_plus_omega_t0_over_a_sigma", 1.0 + omega_t0 / a_sigma),
        ("one_plus_omega_t0_times_abs_eta", 1.0 + 2.0 * omega_t0),
        ("one_plus_one_minus_a_sigma_over_50", 1.0 + (1.0 - a_sigma) / 50.0),
        ("one_plus_z_sigma_over_75", 1.0 + z_sigma / 75.0),
        ("one_plus_one_over_150", 1.0 + 1.0 / 150.0),
        ("one_plus_one_over_144", 1.0 + 1.0 / 144.0),
        ("one_plus_one_over_128", 1.0 + 1.0 / 128.0),
    ]
    rows = []
    for name, factor in raw:
        value = base * factor
        residual = value - target
        rows.append(
            {
                "name": name,
                "factor": factor,
                "value": value,
                "target": target,
                "abs_residual": abs(residual),
                "relative_residual": abs(residual) / target,
            }
        )
    return rows


def build_payload() -> dict:
    delta = delta_payload()
    constants, _ = master_branch_background()
    target = float(delta["target_delta_Neff"])
    base = float(delta["best_candidate"]["value"])
    exact_factor = target / base
    rows = correction_candidates(constants, target, base)
    best = min(rows, key=lambda row: row["abs_residual"])
    return {
        "description": "Residual closure attempt for Delta N_eff = |eta_H| Omega_m0 plus a small Janus correction.",
        "status": "delta-neff-residual-closure-attempted",
        "target_delta_Neff": target,
        "base_delta_Neff": base,
        "exact_required_factor": exact_factor,
        "exact_required_fractional_correction": exact_factor - 1.0,
        "candidates": rows,
        "best_candidate": best,
        "subpercent_residual_closed": best["relative_residual"] < 0.001,
        "is_derived_geometry": False,
        "next_required": "derive the residual factor multiplying |eta_H| Omega_m0 from the early Holst plasma normalization.",
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Delta Neff Residual Closure",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Derived geometry: {payload['is_derived_geometry']}",
        "",
        "## Exact Residual",
        "",
        f"- target Delta N_eff: {payload['target_delta_Neff']:.6g}",
        f"- base |eta_H| Omega_m0: {payload['base_delta_Neff']:.6g}",
        f"- exact required factor: {payload['exact_required_factor']:.6g}",
        f"- exact required fractional correction: {payload['exact_required_fractional_correction']:.6g}",
        "",
        "## Candidates",
        "",
        "| name | factor | value | relative residual |",
        "|---|---:|---:|---:|",
    ]
    for row in sorted(payload["candidates"], key=lambda item: item["abs_residual"]):
        lines.append(
            f"| {row['name']} | {row['factor']:.6g} | "
            f"{row['value']:.6g} | {row['relative_residual']:.6g} |"
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
