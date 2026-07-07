from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
INPUT_PATH = BASE / "global_action_angle_alpha_quantization_inputs.json"
OUTPUT_PATH = BASE / "published_exact_solution_scale_inputs.json"
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_global_action_angle_alpha_quantization_gate.json"
)
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_global_action_angle_alpha_quantization_gate.md"
)
HBAR_J_S = 1.054571817e-34


def _read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def _positive(value: Any) -> bool:
    return isinstance(value, (int, float)) and float(value) > 0.0


def alpha_from_action_integral(
    *, action_prefactor_SI: float, alpha_power: float, integer_n: int, hbar_J_s: float = HBAR_J_S
) -> float:
    if action_prefactor_SI <= 0.0:
        raise ValueError("action_prefactor_SI must be positive")
    if alpha_power <= 0.0:
        raise ValueError("alpha_power must be positive")
    if integer_n == 0:
        raise ValueError("integer_n must be nonzero")
    return ((2.0 * math.pi * hbar_J_s * abs(integer_n)) / action_prefactor_SI) ** (
        1.0 / alpha_power
    )


def build_payload(
    input_path: Path = INPUT_PATH,
    output_path: Path = OUTPUT_PATH,
    *,
    write_output: bool = False,
) -> dict[str, Any]:
    data = _read(input_path)
    checks = {
        "published_exact_orbit_shape_available": True,
        "global_PT_cycle_identified": bool(data.get("global_PT_cycle_identified")),
        "cycle_is_compact_closed": bool(data.get("cycle_is_compact_closed")),
        "canonical_pair_qp_derived": bool(data.get("canonical_pair_qp_derived")),
        "symplectic_one_form_theta_derived": bool(
            data.get("symplectic_one_form_theta_derived")
        ),
        "action_integral_I_alpha_derived": bool(
            data.get("action_integral_I_alpha_derived")
        ),
        "action_prefactor_SI_available": _positive(data.get("action_prefactor_SI")),
        "alpha_power_available": _positive(data.get("alpha_power")),
        "bohr_sommerfeld_law_accepted": bool(data.get("bohr_sommerfeld_law_accepted")),
        "primitive_integer_n_available": isinstance(data.get("integer_n"), int)
        and data.get("integer_n") != 0,
        "primitive_sector_selected": bool(data.get("primitive_sector_selected")),
    }
    ready = all(checks.values())
    alpha_seconds = None
    output = None
    if ready:
        alpha_seconds = alpha_from_action_integral(
            action_prefactor_SI=float(data["action_prefactor_SI"]),
            alpha_power=float(data["alpha_power"]),
            integer_n=int(data["integer_n"]),
            hbar_J_s=float(data.get("hbar_J_s", HBAR_J_S)),
        )
        output = {
            "active_core": "Z2_tunnel_Sigma",
            "alpha_seconds": alpha_seconds,
            "scale_provenance": "global_action_angle_quantization",
            "observational_fit_used": False,
            "compressed_planck_lcdm_background_used": False,
            "archived_z4_reuse_used": False,
        }
        if write_output:
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")

    return {
        "status": "janus-z2-global-action-angle-alpha-quantization-gate",
        "active_core": "Z2_tunnel_Sigma",
        "checks": checks,
        "action_angle_alpha_quantized": ready,
        "alpha_seconds": alpha_seconds,
        "blocked_by": [key for key, ok in checks.items() if not ok],
        "core_result": (
            "The exact Janus orbit gives a dimensionless alpha-family, but not "
            "a canonical action variable. Bohr-Sommerfeld quantization fixes "
            "alpha only after a compact PT cycle, theta, and I(alpha) are "
            "derived. Without them this is a new global quantum postulate, not "
            "a derived Janus/Z2/Sigma prediction."
        ),
        "formula_if_derived": "If I(alpha)=K alpha^p, alpha_n=(2*pi*hbar*|n|/K)^(1/p).",
        "published_exact_solution_scale_inputs_written": output is not None,
        "output_payload": output,
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload(write_output=True)
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2 Global Action-Angle Alpha Quantization Gate",
                "",
                f"Action-angle alpha quantized: `{payload['action_angle_alpha_quantized']}`",
                "",
                payload["core_result"],
                "",
                f"Formula if derived: `{payload['formula_if_derived']}`",
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
