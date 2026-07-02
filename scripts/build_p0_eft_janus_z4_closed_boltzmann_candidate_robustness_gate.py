from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_closed_boltzmann_candidate_robustness_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_closed_boltzmann_candidate_robustness_gate.json")
TRIAL_JSON = Path("outputs/reports/p0_eft_janus_z4_official_planck_closed_boltzmann_acoustic_polarization_trial.json")
HIERARCHY_JSON = Path("outputs/reports/p0_eft_janus_z4_photon_polarization_boltzmann_hierarchy_closure_gate.json")


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def _curvature(rows: dict, t: float, e: float) -> dict:
    center = rows.get(f"{t},{e}", {}).get("delta_chi2_joint")
    left = rows.get(f"{t-0.002},{e}", {}).get("delta_chi2_joint")
    right = rows.get(f"{t+0.002},{e}", {}).get("delta_chi2_joint")
    down = rows.get(f"{t},{e-0.005}", {}).get("delta_chi2_joint")
    up = rows.get(f"{t},{e+0.005}", {}).get("delta_chi2_joint")
    return {
        "center": center,
        "lambda_T_curvature_positive": bool(left is not None and center is not None and right is not None and left > center and right > center),
        "lambda_E_curvature_positive": bool(down is not None and center is not None and up is not None and down > center and up > center),
        "neighbors": {
            "lambda_T_left": left,
            "lambda_T_right": right,
            "lambda_E_down": down,
            "lambda_E_up": up,
        },
    }


def build_payload() -> dict:
    trial = _load(TRIAL_JSON)
    hierarchy = _load(HIERARCHY_JSON)
    rows = trial.get("trial_rows", {})
    best = trial.get("best_summary", {})
    best_t = best.get("lambda_T")
    best_e = best.get("lambda_E")
    edge = bool(best_t in (-1.0e-2, -6.0e-3) or best_e in (-2.5e-2, -1.5e-2))
    curv = _curvature(rows, float(best_t), float(best_e)) if best_t is not None and best_e is not None else {}
    gain = best.get("delta_chi2_joint")
    gain_survives = bool(gain is not None and gain < -5.0)
    transport = bool(trial.get("transport_guards_passed"))
    hierarchy_ok = bool(
        hierarchy.get("TCA_switch_smoothness_passed")
        and hierarchy.get("strong_TCA_suppression_passed")
        and hierarchy.get("lmax_convergence_passed")
    )
    local_curvature = bool(curv.get("lambda_T_curvature_positive") and curv.get("lambda_E_curvature_positive"))
    robust = bool(
        trial.get("boltzmann_closed_effective_z4_cmb_candidate")
        and gain_survives
        and transport
        and hierarchy_ok
        and local_curvature
        and not edge
    )
    return {
        "status": "janus-z4-closed-boltzmann-candidate-robustness-gate",
        "source_trial": str(TRIAL_JSON),
        "source_hierarchy_gate": str(HIERARCHY_JSON),
        "best_point": {
            "lambda_T": best_t,
            "lambda_E": best_e,
            "delta_chi2": gain,
            "interaction_term": best.get("interaction_term"),
        },
        "best_point_stable": bool(local_curvature and not edge),
        "local_curvature_detected": local_curvature,
        "lambda_best_not_edge": not edge,
        "gain_survives_lmax_variation": bool(hierarchy.get("lmax_convergence_passed")),
        "gain_survives_TCA_switch_variation": bool(hierarchy.get("TCA_switch_smoothness_passed")),
        "delta_chi2_available_remains_below_minus_5": gain_survives,
        "TE_EE_smoothness_remains_pass": transport,
        "transport_guards_remain_pass": transport,
        "lmax_convergence_remains_pass": bool(hierarchy.get("lmax_convergence_passed")),
        "curvature_diagnostics": curv,
        "closed_boltzmann_candidate_robustness_gate_passed": robust,
        "full_planck_verdict": False,
        "next_required_action": (
            "document robust effective candidate; do not open new physics before likelihood completeness is resolved"
            if robust
            else "inspect local curvature/transport before promoting robustness"
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Closed-Boltzmann Candidate Robustness Gate",
        "",
        f"Gate passed: `{payload['closed_boltzmann_candidate_robustness_gate_passed']}`",
        f"Best point stable: `{payload['best_point_stable']}`",
        f"Local curvature detected: `{payload['local_curvature_detected']}`",
        f"Lambda best not edge: `{payload['lambda_best_not_edge']}`",
        f"Gain survives threshold: `{payload['delta_chi2_available_remains_below_minus_5']}`",
        f"Full Planck verdict: `{payload['full_planck_verdict']}`",
        "",
        payload["next_required_action"],
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
