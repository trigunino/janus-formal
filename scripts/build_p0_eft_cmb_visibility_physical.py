from __future__ import annotations

from pathlib import Path
import json
import math

try:
    from scripts.build_p0_eft_early_holst_plasma_stress_tensor import build_payload as stress_payload
    from scripts.build_p0_eft_janus_holst_distance_ruler_map import trapezoid_integral
except ModuleNotFoundError:
    from build_p0_eft_early_holst_plasma_stress_tensor import build_payload as stress_payload
    from build_p0_eft_janus_holst_distance_ruler_map import trapezoid_integral


REPORT_PATH = Path("outputs/reports/p0_eft_cmb_visibility_physical.md")
JSON_PATH = Path("outputs/reports/p0_eft_cmb_visibility_physical.json")


def visibility_parameters(delta_neff: float) -> dict:
    z_star_ref = 1089.0
    sigma_ref = 85.0
    expansion_boost = math.sqrt(1.0 + 0.2271 * delta_neff / (1.0 + 0.2271 * 3.046))
    return {
        "z_star": z_star_ref * expansion_boost ** 0.08,
        "sigma_z": sigma_ref / expansion_boost ** 0.5,
        "expansion_boost": expansion_boost,
    }


def visibility_physical(z: float, z_star: float, sigma_z: float) -> float:
    x = (z - z_star) / sigma_z
    return math.exp(-0.5 * x * x)


def build_payload() -> dict:
    stress = stress_payload()
    params = visibility_parameters(float(stress["derived_delta_Neff"]))
    zs = [700.0 + (1400.0 - 700.0) * i / 1000 for i in range(1001)]
    raw = [visibility_physical(z, params["z_star"], params["sigma_z"]) for z in zs]
    norm = trapezoid_integral(zs, raw)
    normalized = [v / norm for v in raw]
    mean_z = trapezoid_integral(zs, [z * v for z, v in zip(zs, normalized)])
    variance = trapezoid_integral(zs, [(z - mean_z) ** 2 * v for z, v in zip(zs, normalized)])
    return {
        "description": "Physicalized recombination visibility target with Janus-Holst Delta_Neff expansion boost.",
        "status": "cmb-visibility-physical-target-derived",
        "Delta_Neff_Holst": stress["derived_delta_Neff"],
        "z_star": params["z_star"],
        "sigma_z": params["sigma_z"],
        "expansion_boost": params["expansion_boost"],
        "normalization": trapezoid_integral(zs, normalized),
        "mean_z": mean_z,
        "sigma_z_measured": math.sqrt(variance),
        "visibility_function_ready": True,
        "is_full_recombination_solver": False,
        "next_required": "replace this physicalized visibility target with a recombination ODE solver for final Planck likelihood.",
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT CMB Visibility Physical",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Visibility ready: {payload['visibility_function_ready']}",
        f"Full recombination solver: {payload['is_full_recombination_solver']}",
        "",
        "## Parameters",
        "",
        f"- Delta N_eff Holst: {payload['Delta_Neff_Holst']:.6g}",
        f"- expansion boost: {payload['expansion_boost']:.6g}",
        f"- z_star: {payload['z_star']:.6g}",
        f"- sigma_z: {payload['sigma_z']:.6g}",
        f"- normalization: {payload['normalization']:.6g}",
        f"- measured mean z: {payload['mean_z']:.6g}",
        f"- measured sigma_z: {payload['sigma_z_measured']:.6g}",
        "",
        "## Next",
        "",
        payload["next_required"],
        "",
    ]
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
