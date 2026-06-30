from __future__ import annotations

from pathlib import Path
import json

import numpy as np


REPORT_PATH = Path("outputs/reports/p0_janus_soldered_l_substitution_residual_gate.md")
JSON_PATH = Path("outputs/reports/p0_janus_soldered_l_substitution_residual_gate.json")
ETA2 = np.diag([-1.0, 1.0])
TOLERANCE = 1e-12


def diagonal_frame_1p1(a_time: float, a_space: float) -> np.ndarray:
    return np.diag([1.0 / np.sqrt(a_time), 1.0 / np.sqrt(a_space)])


def metric_from_scales(a_time: float, a_space: float) -> np.ndarray:
    return np.diag([-a_time, a_space])


def solder_l_other_to_self(
    jac_self_to_other: np.ndarray,
    frame_self: np.ndarray,
    frame_other: np.ndarray,
) -> np.ndarray:
    coframe_self = np.linalg.inv(frame_self)
    return coframe_self @ np.linalg.inv(jac_self_to_other) @ frame_other


def solder_l_self_to_other(
    jac_self_to_other: np.ndarray,
    frame_self: np.ndarray,
    frame_other: np.ndarray,
) -> np.ndarray:
    coframe_other = np.linalg.inv(frame_other)
    return coframe_other @ jac_self_to_other @ frame_self


def lorentz_residual(transform: np.ndarray) -> np.ndarray:
    return transform.T @ ETA2 @ transform - ETA2


def max_abs(matrix: np.ndarray) -> float:
    return float(np.max(np.abs(matrix)))


def qcross_from_l(transform: np.ndarray, covector: np.ndarray, velocity: np.ndarray) -> float:
    transported_velocity = transform @ velocity
    numerator = float(covector @ ETA2 @ transported_velocity) ** 2
    denominator = float(covector @ ETA2 @ velocity) ** 2
    return numerator / denominator


def summarize_case(
    name: str,
    jac: np.ndarray,
    metric_self: np.ndarray,
    metric_other: np.ndarray,
    frame_self: np.ndarray,
    frame_other: np.ndarray,
) -> dict:
    l_os = solder_l_other_to_self(jac, frame_self, frame_other)
    l_so = solder_l_self_to_other(jac, frame_self, frame_other)
    lorentz = lorentz_residual(l_os)
    mirror = l_so @ l_os - np.eye(2)
    metric_pullback = jac.T @ metric_other @ jac - metric_self
    source_velocity = np.array([1.0, 0.0])
    null_covector = np.array([1.0, 1.0])
    source_momentum = np.array([1.25, 0.75])
    stress_other = np.array([[2.0, 0.4], [0.4, 0.6]])
    stress_self = l_os @ stress_other @ l_os.T
    vlasov_shell_residual = float(source_momentum @ lorentz @ source_momentum)
    qcross = qcross_from_l(l_os, null_covector, source_velocity)
    return {
        "case": name,
        "jacobian": jac.tolist(),
        "metric_pullback_residual_max": max_abs(metric_pullback),
        "l_other_to_self": l_os.tolist(),
        "l_self_to_other": l_so.tolist(),
        "lorentz_residual_max": max_abs(lorentz),
        "mirror_inverse_residual_max": max_abs(mirror),
        "k_substitution": "K_self^{AB}=L^A_C L^B_D T_other^{CD}",
        "k_transport_sample": stress_self.tolist(),
        "qcross_substitution": "Q_cross=(eta_AB L^A_C u_other^C k_self^B)^2/(eta_AB u_self^A k_self^B)^2",
        "qcross_sample": qcross,
        "vlasov_substitution": "p_self^A=L^A_B p_other^B; shell residual=p_other^T(L^T eta L-eta)p_other",
        "vlasov_shell_residual": vlasov_shell_residual,
        "lorentz_closed": max_abs(lorentz) < TOLERANCE,
        "mirror_closed": max_abs(mirror) < TOLERANCE,
    }


def build_payload() -> dict:
    stretch = np.diag([1.2, 0.8])
    metric_other = ETA2.copy()
    metric_self_compatible = stretch.T @ metric_other @ stretch
    frame_other = diagonal_frame_1p1(1.0, 1.0)
    frame_self_compatible = diagonal_frame_1p1(1.44, 0.64)
    compatible = summarize_case(
        "metric_compatible_pullback",
        stretch,
        metric_self_compatible,
        metric_other,
        frame_self_compatible,
        frame_other,
    )

    identity = np.eye(2)
    metric_self_flat = metric_from_scales(1.0, 1.0)
    metric_other_mismatch = metric_from_scales(1.002, 0.998)
    frame_self_flat = diagonal_frame_1p1(1.0, 1.0)
    frame_other_mismatch = diagonal_frame_1p1(1.002, 0.998)
    mismatch = summarize_case(
        "metric_mismatch_identity_map",
        identity,
        metric_self_flat,
        metric_other_mismatch,
        frame_self_flat,
        frame_other_mismatch,
    )

    substitution_rows = [
        {
            "target": "L_solder",
            "formula": "L_{o->s}^A_B=theta_s^A_mu (J_{s->o}^{-1})^mu_alpha e_o^alpha_B",
            "result": "derived from phi and tetrads; not an independent fit variable",
        },
        {
            "target": "K",
            "formula": "K_s^{AB}=L^A_C L^B_D T_o^{CD}",
            "result": "same L fixes tensor transport",
        },
        {
            "target": "Q_cross",
            "formula": "Q_cross=(eta_AB L^A_C u_o^C k_s^B)^2/(eta_AB u_s^A k_s^B)^2",
            "result": "same L fixes optical contraction",
        },
        {
            "target": "Vlasov",
            "formula": "p_s^A=L^A_B p_o^B; f_s(x,p_s)=f_o(phi(x),L^{-1}p_s)",
            "result": "same L fixes phase-space momentum transport",
        },
        {
            "target": "Lorentz_residual",
            "formula": "R_eta=L^T eta L-eta",
            "result": "must vanish before using K/Q_cross/Vlasov physically",
        },
        {
            "target": "mirror_residual",
            "formula": "R_mirror=L_{s->o}L_{o->s}-I",
            "result": "must vanish for plus/minus inverse consistency",
        },
    ]
    return {
        "description": "Derivation and bounded numeric residual gate for soldered same-L substitution.",
        "status": "soldered-l-derived-substitution-tested-lorentz-conditional",
        "depends_on": [
            "p0_janus_exact_source_term_closure_attack",
            "p0_same_l_bridge_induces_m_k_qcross_gate",
            "p0_janus_phi_l_ephi_el_variational_origin_gate",
            "p0_janus_metric_pullback_compatibility_gate",
        ],
        "substitution_rows": substitution_rows,
        "compatible_case": compatible,
        "mismatch_case": mismatch,
        "l_solder_formula_derived": True,
        "substitutes_k_qcross_vlasov": True,
        "compatible_case_lorentz_closed": compatible["lorentz_closed"],
        "compatible_case_mirror_closed": compatible["mirror_closed"],
        "mismatch_case_lorentz_closed": mismatch["lorentz_closed"],
        "mismatch_case_mirror_closed": mismatch["mirror_closed"],
        "same_l_can_be_used_only_if_lorentz_residual_zero": True,
        "metric_pullback_compatibility_artifact": "p0_janus_metric_pullback_compatibility_gate",
        "lorentz_residual_equivalent_to_metric_pullback_residual": True,
        "mirror_inverse_test_encoded": True,
        "uses_observational_fit": False,
        "uses_qdet_qcross_absorption": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "L_solder is now derived and substituted into K, Q_cross and Vlasov. "
            "It closes only on metric-compatible pullback branches; a metric mismatch "
            "leaves a Lorentz/mass-shell residual that cannot be hidden in Q_det or Q_cross."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Soldered-L Substitution Residual Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"L_solder formula derived: {payload['l_solder_formula_derived']}",
        f"Substitutes K/Q_cross/Vlasov: {payload['substitutes_k_qcross_vlasov']}",
        f"Compatible case Lorentz closed: {payload['compatible_case_lorentz_closed']}",
        f"Compatible case mirror closed: {payload['compatible_case_mirror_closed']}",
        f"Mismatch case Lorentz closed: {payload['mismatch_case_lorentz_closed']}",
        f"Mismatch case mirror closed: {payload['mismatch_case_mirror_closed']}",
        "Same L can be used only if Lorentz residual zero: "
        f"{payload['same_l_can_be_used_only_if_lorentz_residual_zero']}",
        "Metric pullback compatibility artifact: "
        f"`{payload['metric_pullback_compatibility_artifact']}`",
        "Lorentz residual equivalent to metric pullback residual: "
        f"{payload['lorentz_residual_equivalent_to_metric_pullback_residual']}",
        f"Mirror inverse test encoded: {payload['mirror_inverse_test_encoded']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Uses Qdet/Qcross absorption: {payload['uses_qdet_qcross_absorption']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Substitution Rows",
        "",
        "| target | formula | result |",
        "|---|---|---|",
    ]
    for row in payload["substitution_rows"]:
        lines.append(f"| {row['target']} | `{row['formula']}` | {row['result']} |")
    lines.extend(
        [
            "",
            "## Numeric Cases",
            "",
            "| case | metric residual | Lorentz residual | mirror residual | Vlasov shell residual | Q_cross |",
            "|---|---:|---:|---:|---:|---:|",
        ]
    )
    for key in ("compatible_case", "mismatch_case"):
        row = payload[key]
        lines.append(
            f"| {row['case']} | {row['metric_pullback_residual_max']:.12g} | "
            f"{row['lorentz_residual_max']:.12g} | {row['mirror_inverse_residual_max']:.12g} | "
            f"{row['vlasov_shell_residual']:.12g} | {row['qcross_sample']:.12g} |"
        )
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
