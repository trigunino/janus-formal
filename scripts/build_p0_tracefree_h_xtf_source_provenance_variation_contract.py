from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_tracefree_h_janus_coupled_stress_stf_transport_gate import (
    build_payload as build_janus_coupled_stress_stf_transport,
)


REPORT_PATH = Path("outputs/reports/p0_tracefree_h_xtf_source_provenance_variation_contract.md")
JSON_PATH = Path("outputs/reports/p0_tracefree_h_xtf_source_provenance_variation_contract.json")


def build_payload() -> dict:
    coupled_stress_transport = build_janus_coupled_stress_stf_transport()
    source_candidates = [
        {
            "candidate": "janus_coupled_stress_stf",
            "source_shape": "X_TF = P_STF(T_self + B4vol T_other_to_self)",
            "source_anchor": "M15 Eqs. 4a-4b; M30 mixed source equations",
            "conditional_promotion": True,
            "accepted": False,
            "blocker": "needs exact transport of T_other_to_self, same bridge, measure, and full variation",
        },
        {
            "candidate": "Pi_TF",
            "source_shape": "spatial anisotropic stress STF",
            "source_anchor": "stress decomposition, not standalone Janus source",
            "conditional_promotion": True,
            "accepted": False,
            "blocker": "needs 4D congruence lift, matter action, and same-L transport",
        },
        {
            "candidate": "Weyl_shear",
            "source_shape": "electric Weyl/shear STF diagnostic",
            "source_anchor": "weak-lensing/metric diagnostic only",
            "conditional_promotion": True,
            "accepted": False,
            "blocker": "needs Janus field equation tying optical curvature to H_TF/Q_TF",
        },
        {
            "candidate": "Vlasov_quadrupole",
            "source_shape": "second velocity moment STF",
            "source_anchor": "X2025-kinetic-galactic Vlasov/Poisson anchor",
            "conditional_promotion": True,
            "accepted": False,
            "blocker": "needs Janus kinetic action/source, phase-space measure, and closed hierarchy",
        },
        {
            "candidate": "Phi_Sigma_or_N_alpha",
            "source_shape": "relative strain/nonmetricity STF",
            "source_anchor": "candidate geometry only",
            "conditional_promotion": True,
            "accepted": False,
            "blocker": "needs EL source proof, curl integrability, mirror inverse, same-L, stability",
        },
    ]
    variation_ledger = [
        "delta_Q term: 1/2 L_log,H^*[P_STF(X_TF)]",
        "delta_X term: Q_TF^{ab} delta X_TF_ab over H,L,phi,matter dependencies",
        "delta_P_STF term: projector/metric/congruence variation",
        "delta_mu term: action-measure variation, not an STF source by itself",
        "boundary/gauge terms: must be fixed before dropping integrations by parts",
    ]
    acceptance_tests = [
        "published/source-action provenance for chosen X_TF",
        "covariant 4D symmetric trace-free rank-2 type",
        "same bridge/tetrad/L/congruence/measure as Q_TF, K and Q_cross",
        "full dependency variation ledger closed",
        "no residual fit, scalar trace, determinant/B4vol trace, or screen-only shortcut",
        "prediction remains false until R_plus=R_minus=0 with same phi/L/B4vol",
    ]
    return {
        "description": "Contract for promoting a candidate X_TF into the linear Q_TF X_TF H-EL source.",
        "status": "xtf-source-provenance-variation-contract-open",
        "target_channel": "H_TF/Q_TF",
        "best_non_rustine_candidate": "janus_coupled_stress_stf",
        "best_candidate_source_shape": "X_TF = P_STF(T_self + B4vol T_other_to_self)",
        "best_candidate_source_anchors": ["M15 Eqs. 4a-4b", "M30 mixed source equations"],
        "coupled_stress_transport_artifact": "p0_tracefree_h_janus_coupled_stress_stf_transport_gate",
        "coupled_stress_transport_algebra_closed": bool(
            coupled_stress_transport["algebraic_transport_closed"]
        ),
        "coupled_stress_transport_acceptance_closed": bool(
            coupled_stress_transport["transport_acceptance_closed"]
        ),
        "same_l_bridge_stack_artifact": coupled_stress_transport["same_l_bridge_stack_artifact"],
        "same_l_bridge_stack_algebra_closed": bool(
            coupled_stress_transport["same_l_bridge_stack_algebra_closed"]
        ),
        "same_l_bridge_stack_source_selected": bool(
            coupled_stress_transport["same_l_bridge_stack_source_selected"]
        ),
        "source_candidates": source_candidates,
        "candidate_count": len(source_candidates),
        "accepted_candidates": [],
        "any_candidate_accepted": False,
        "variation_ledger": variation_ledger,
        "acceptance_tests": acceptance_tests,
        "contract_closed": False,
        "source_action_provenance_closed": False,
        "same_bridge_closed": False,
        "dependency_variation_closed": False,
        "physics_closed": False,
        "prediction": False,
        "prediction_ready": False,
        "verdict": (
            "The best non-rustine X_TF target is the STF projection of the Janus "
            "coupled stress source, not a new fitted tensor. It is still not accepted "
            "until transport, same-bridge, measure and variation obligations close."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Trace-Free H X_TF Source Provenance Variation Contract",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Target channel: {payload['target_channel']}",
        f"Best non-rustine candidate: `{payload['best_non_rustine_candidate']}`",
        f"Best candidate source shape: `{payload['best_candidate_source_shape']}`",
        f"Coupled-stress transport artifact: `{payload['coupled_stress_transport_artifact']}`",
        f"Coupled-stress transport algebra closed: {payload['coupled_stress_transport_algebra_closed']}",
        f"Coupled-stress transport acceptance closed: {payload['coupled_stress_transport_acceptance_closed']}",
        f"Same-L bridge stack artifact: `{payload['same_l_bridge_stack_artifact']}`",
        f"Same-L bridge stack algebra closed: {payload['same_l_bridge_stack_algebra_closed']}",
        f"Same-L bridge stack source selected: {payload['same_l_bridge_stack_source_selected']}",
        f"Any candidate accepted: {payload['any_candidate_accepted']}",
        f"Contract closed: {payload['contract_closed']}",
        f"Prediction: {payload['prediction']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Source Candidates",
        "",
        "| candidate | source shape | anchor | conditional | accepted | blocker |",
        "|---|---|---|---:|---:|---|",
    ]
    for row in payload["source_candidates"]:
        lines.append(
            f"| {row['candidate']} | `{row['source_shape']}` | {row['source_anchor']} | "
            f"{row['conditional_promotion']} | {row['accepted']} | {row['blocker']} |"
        )
    lines.extend(["", "## Variation Ledger", ""])
    lines.extend(f"- {item}" for item in payload["variation_ledger"])
    lines.extend(["", "## Acceptance Tests", ""])
    lines.extend(f"- {item}" for item in payload["acceptance_tests"])
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
