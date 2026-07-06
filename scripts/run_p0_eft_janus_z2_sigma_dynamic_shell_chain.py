from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_flrw_extrinsic_curvature_grid_writer_gate import (
    build_payload as write_k_grid,
)
from scripts.write_p0_eft_janus_z2_cover_sigma_alpha_h_from_surface_hk import (
    build_payload as write_sigma_alpha_h,
)
from scripts.write_p0_eft_janus_z2_sigma_dynamic_shell_inputs_from_rsigma_and_bulk_f import (
    build_payload as write_dynamic_shell,
)
from scripts.write_p0_eft_janus_z2_sigma_flrw_extrinsic_curvature_from_dynamic_shell import (
    build_payload as write_k_grid_inputs,
)
from scripts.write_p0_eft_janus_z2_sigma_radius_kinematics_from_rsigma import (
    build_payload as write_radius_kinematics,
)
from scripts.write_p0_eft_janus_z2_sigma_rsigma_radius_solution_from_isotropic_balance import (
    build_payload as write_radius_solution,
)
from scripts.write_p0_eft_janus_z2_sigma_surface_hk_isotropic_geometry import (
    build_payload as write_surface_hk_geometry,
)
from scripts.run_p0_eft_janus_z2_sigma_counterterm_chain import (
    build_payload as run_counterterm_chain,
)


BASE = Path("outputs/active_z2_sigma")
COVER = Path("outputs/active_z2_cover")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_dynamic_shell_chain.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_dynamic_shell_chain.json")


def _step_passed(payload: dict) -> bool:
    return bool(
        payload.get("gate_passed")
        or payload.get("chain_passed")
        or payload.get("sigma_alpha_h_inputs_written")
    )


def _blocker(payload: dict) -> str:
    if payload.get("first_blocker"):
        return str(payload["first_blocker"])
    if payload.get("primary_blocker") == "rsigma_solution_certificate_missing":
        return "rsigma_radius_solution_or_certificate_missing"
    if payload.get("primary_blocker"):
        return str(payload["primary_blocker"])
    missing = payload.get("missing_inputs")
    if missing:
        return "missing inputs: " + ", ".join(str(item) for item in missing)
    return str(payload.get("validation_error") or "unknown")


def build_payload(
    *,
    base: Path = BASE,
    cover: Path = COVER,
) -> dict:
    paths = {
        "rsigma_certificate": base / "rsigma_solution_certificate.json",
        "rsigma_radius_solution": base / "rsigma_radius_solution.json",
        "radius_kinematics": base / "dynamic_shell_radius_kinematics_inputs.json",
        "bulk_f_pm": base / "static_areal_bulk_f_pm_inputs.json",
        "dynamic_shell": base / "dynamic_shell_extrinsic_curvature_inputs.json",
        "k_grid_inputs": base / "flrw_extrinsic_curvature_grid_inputs.json",
        "k_grid": base / "flrw_extrinsic_curvature_grid.json",
        "surface_hk_geometry": base / "surface_hk_isotropic_geometry.json",
        "surface_hk_coefficients": base / "surface_hk_active_density_coefficients.json",
        "sigma_alpha_h": cover / "sigma_alpha_h_inputs.json",
    }

    steps: list[dict] = []
    step_specs = [
        (
            "counterterm_chain_for_rsigma_balance",
            lambda: {"gate_passed": True, "status": "existing-rsigma-counterterm"}
            if paths["rsigma_radius_solution"].exists()
            or (base / "rsigma_E_counterterm.json").exists()
            else run_counterterm_chain(base=base),
        ),
        (
            "rsigma_radius_solution",
            lambda: {"gate_passed": True, "status": "existing-rsigma-radius-solution"}
            if paths["rsigma_radius_solution"].exists()
            else write_radius_solution(output_path=paths["rsigma_radius_solution"]),
        ),
        (
            "radius_kinematics",
            lambda: write_radius_kinematics(
                input_path=paths["rsigma_radius_solution"]
                if paths["rsigma_radius_solution"].exists()
                else paths["rsigma_certificate"],
                output_path=paths["radius_kinematics"],
            ),
        ),
        (
            "dynamic_shell_inputs",
            lambda: write_dynamic_shell(
                certificate_path=paths["rsigma_radius_solution"]
                if paths["rsigma_radius_solution"].exists()
                else paths["rsigma_certificate"],
                kinematics_path=paths["radius_kinematics"],
                bulk_f_path=paths["bulk_f_pm"],
                output_path=paths["dynamic_shell"],
            ),
        ),
        (
            "flrw_extrinsic_curvature_grid_inputs",
            lambda: write_k_grid_inputs(
                input_path=paths["dynamic_shell"],
                output_path=paths["k_grid_inputs"],
            ),
        ),
        (
            "flrw_extrinsic_curvature_grid",
            lambda: write_k_grid(
                input_path=paths["k_grid_inputs"],
                output_path=paths["k_grid"],
            ),
        ),
        (
            "surface_hk_isotropic_geometry",
            lambda: write_surface_hk_geometry(
                input_path=paths["k_grid"],
                output_path=paths["surface_hk_geometry"],
            ),
        ),
        (
            "sigma_alpha_h_inputs",
            lambda: write_sigma_alpha_h(
                coeff_path=paths["surface_hk_coefficients"],
                geom_path=paths["surface_hk_geometry"],
                output_path=paths["sigma_alpha_h"],
            ),
        ),
    ]

    first_blocker = None
    for name, run in step_specs:
        payload = run()
        passed = _step_passed(payload)
        steps.append(
            {
                "name": name,
                "passed": passed,
                "blocker": None if passed else _blocker(payload),
                "payload_status": payload.get("status"),
            }
        )
        if not passed:
            first_blocker = steps[-1]["blocker"]
            break

    return {
        "status": "janus-z2-sigma-dynamic-shell-chain",
        "active_core": "Z2_tunnel_Sigma",
        "steps": steps,
        "chain_passed": first_blocker is None,
        "first_blocker": first_blocker or "none",
        "paths": {key: str(path) for key, path in paths.items()},
        "forbidden_shortcuts": [
            "no guessed R_Sigma",
            "no guessed f_pm",
            "no E_counterterm_zero assumption",
            "no archived Z4 inputs",
            "no observational fit",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Dynamic Shell Chain",
        "",
        f"Passed: `{payload['chain_passed']}`",
        f"First blocker: `{payload['first_blocker']}`",
        "",
        "## Steps",
    ]
    lines.extend(
        f"- `{step['name']}`: `{step['passed']}`"
        + ("" if step["passed"] else f" ({step['blocker']})")
        for step in payload["steps"]
    )
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
