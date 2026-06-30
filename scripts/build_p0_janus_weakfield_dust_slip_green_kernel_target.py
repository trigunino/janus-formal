from __future__ import annotations

from pathlib import Path
import json

import numpy as np


REPORT_PATH = Path("outputs/reports/p0_janus_weakfield_dust_slip_green_kernel_target.md")
JSON_PATH = Path("outputs/reports/p0_janus_weakfield_dust_slip_green_kernel_target.json")
TOLERANCE = 1e-12


def determinant(k2: float, chi: float, rho_minus_to_plus: float, rho_plus_to_minus: float) -> float:
    return 4.0 * k2 * (k2 + chi * (rho_minus_to_plus - rho_plus_to_minus))


def source_compatibility(source_plus: float, source_minus: float, rho_minus_to_plus: float, rho_plus_to_minus: float) -> float:
    return source_minus * rho_minus_to_plus + source_plus * rho_plus_to_minus


def solve_mode(
    k2: float,
    chi: float,
    rho_minus_to_plus: float,
    rho_plus_to_minus: float,
    source_plus: float,
    source_minus: float,
    tolerance: float = TOLERANCE,
) -> dict:
    if abs(k2) <= tolerance:
        compatibility = source_compatibility(source_plus, source_minus, rho_minus_to_plus, rho_plus_to_minus)
        if abs(compatibility) > tolerance:
            return {
                "mode": "zero",
                "solvable": False,
                "reason": "source_compatibility_failed",
                "compatibility_residual": compatibility,
            }
        if abs(rho_minus_to_plus) > tolerance:
            delta = source_plus / (2.0 * rho_minus_to_plus)
        elif abs(rho_plus_to_minus) > tolerance:
            delta = -source_minus / (2.0 * rho_plus_to_minus)
        else:
            delta = 0.0
        return {
            "mode": "zero",
            "solvable": True,
            "reason": "common_mode_gauge_fixed",
            "compatibility_residual": compatibility,
            "psi_plus": -0.5 * delta,
            "psi_minus": 0.5 * delta,
        }

    det = determinant(k2, chi, rho_minus_to_plus, rho_plus_to_minus)
    if abs(det) <= tolerance:
        return {
            "mode": "finite",
            "solvable": False,
            "reason": "mass_gap_resonance",
            "determinant": det,
        }

    matrix = np.array(
        [
            [-2.0 * k2 - 2.0 * chi * rho_minus_to_plus, 2.0 * chi * rho_minus_to_plus],
            [-2.0 * chi * rho_plus_to_minus, -2.0 * k2 + 2.0 * chi * rho_plus_to_minus],
        ],
        dtype=float,
    )
    rhs = np.array([chi * source_plus, -chi * source_minus], dtype=float)
    psi_plus, psi_minus = np.linalg.solve(matrix, rhs)
    return {
        "mode": "finite",
        "solvable": True,
        "reason": "finite_mode_inverted",
        "determinant": det,
        "psi_plus": float(psi_plus),
        "psi_minus": float(psi_minus),
    }


def build_payload() -> dict:
    sample_modes = [
        solve_mode(0.0, 1.0, 2.0, 3.0, 4.0, -6.0),
        solve_mode(0.0, 1.0, 2.0, 3.0, 1.0, 1.0),
        solve_mode(5.0, 1.0, 2.0, 3.0, 4.0, -1.0),
        solve_mode(1.0, 1.0, 2.0, 3.0, 4.0, -1.0),
    ]
    return {
        "description": (
            "Diagnostic Green-kernel target for the conditional dust/slip Fourier solver. "
            "It gives admissible mode handling without selecting physical normalization."
        ),
        "status": "dust-slip-green-kernel-target-open",
        "depends_on": [
            "p0_janus_weakfield_dust_slip_fourier_solver_gate",
            "p0_janus_weakfield_zero_mode_background_gauge_gate",
        ],
        "mode_policy": [
            "k2=0 requires source compatibility before any gauge choice",
            "compatible k2=0 fixes only common additive potential gauge",
            "finite modes invert the 2x2 coupled operator when determinant is nonzero",
            "mass-gap resonance blocks the mode until the background branch is source-selected",
        ],
        "sample_modes": sample_modes,
        "green_kernel_written": True,
        "zero_mode_policy_written": True,
        "resonance_policy_written": True,
        "background_branch_selected": False,
        "boundary_conditions_source_derived": False,
        "qdet_convention_selected_from_source": False,
        "same_l_qcross_selected": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "This is a diagnostic kernel target only. It can drive tests or PM probes, "
            "but prediction remains blocked by source-selected background, boundary, Q_det, and same-L gates."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Weak-Field Dust Slip Green Kernel Target",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Green kernel written: {payload['green_kernel_written']}",
        f"Zero-mode policy written: {payload['zero_mode_policy_written']}",
        f"Resonance policy written: {payload['resonance_policy_written']}",
        f"Background branch selected: {payload['background_branch_selected']}",
        f"Boundary conditions source-derived: {payload['boundary_conditions_source_derived']}",
        f"Q_det convention selected from source: {payload['qdet_convention_selected_from_source']}",
        f"Same-L Q_cross selected: {payload['same_l_qcross_selected']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Mode Policy",
        "",
    ]
    lines.extend(f"- {item}" for item in payload["mode_policy"])
    lines.extend(["", "## Sample Modes", "", "| mode | solvable | reason |", "|---|---|---|"])
    for row in payload["sample_modes"]:
        lines.append(f"| {row['mode']} | {row['solvable']} | {row['reason']} |")
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.parent.mkdir(parents=True, exist_ok=True)
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
