from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_dirac_cartan_aps_pt_reduction.md")
JSON_PATH = Path("outputs/reports/p0_eft_dirac_cartan_aps_pt_reduction.json")


def build_payload() -> dict:
    domain = {
        "operator": "Dirac-Cartan Janus operator D_JC = i gamma^mu nabla_mu",
        "space": "L2 spinors on the compact Janus orbifold with fixed hypersurface Sigma",
        "boundary_condition": "APS spectral projection Pi_{>0}(psi|_Sigma)=0",
        "fredholm_goal": "APS domain makes D_JC a Fredholm/self-adjoint spectral problem",
    }
    pt_reduction = {
        "pin_structure": "Pin-",
        "pt_square": "-1",
        "required_relation": "PT must reverse the Dirac spectrum: PT D_JC PT^-1 = -D_JC",
        "commutation_warning": "PT D_JC = D_JC PT is not enough to force eta cancellation",
        "clifford_lift_rule": "Pin- PT lift must transform the Clifford generator with spectral sign reversal",
        "aps_domain_rule": "PT must map Dom_APS(D_JC) to itself, not only swap formal boundary eigenspaces",
        "boundary_chirality_rule": "boundary chirality projection is the extra condition that can make APS invariant",
        "orbifold_tetrad_rule": "Janus soldering must force the frame transition E_plus -> -E_minus",
        "spectral_projector_compensation": "PT Pi_>0 PT^-1 = Pi_<0 must be compensated by the boundary chirality rule",
        "trace_torsion_source": "q_T=1 trace torsion is the candidate geometric source of the boundary chirality projector",
        "pairing": "nonzero eigenvalues pair as (lambda, -lambda)",
        "eta_mod2": "0 conditionally",
    }
    theorem_status = {
        "dirac_cartan_domain_specified": True,
        "aps_boundary_condition_specified": True,
        "pt_commutation_rejected_as_insufficient": True,
        "pt_sign_reversal_reduction_encoded": True,
        "pin_minus_clifford_lift_rule_encoded": True,
        "aps_domain_invariance_rule_encoded": True,
        "boundary_chirality_condition_encoded": True,
        "orbifold_tetrad_sign_rule_encoded": True,
        "projector_compensation_rule_encoded": True,
        "trace_torsion_chirality_source_encoded": True,
        "eta_zero_if_sign_reversal_proved": True,
        "orbifold_tetrad_sign_rule_proved_from_janus_geometry": False,
        "trace_torsion_chirality_source_proved": False,
        "projector_compensation_proved": False,
        "pin_minus_clifford_lift_proved_from_janus_geometry": False,
        "aps_domain_invariance_proved_from_janus_geometry": False,
        "pt_sign_reversal_proved_from_janus_geometry": False,
        "pin_minus_selected_proved": False,
        "prediction_ready": False,
    }
    obligations = [
        "derive the orbifold tetrad sign transition E_plus -> -E_minus from Janus soldering",
        "derive the Pin- Clifford lift rule from the Janus spin/Pin geometry",
        "derive PT D_JC PT^-1 = -D_JC from the Clifford lift and Cartan torsion terms",
        "derive the q_T=1 trace-torsion boundary chirality projector",
        "prove PT Pi_>0 PT^-1 = Pi_<0 is compensated by boundary chirality",
        "prove the APS domain is preserved, not merely exchanged with the opposite projector",
        "derive the boundary chirality projection from the Janus membrane geometry",
        "prove zero modes have even mod-2 contribution or are absent",
        "then promote eta_mod2_zero from conditional to proved",
    ]
    return {
        "description": "APS/PT spectral-reduction target for the Janus Dirac-Cartan EFT route.",
        "status": "conditional-spectral-reduction-open",
        "domain": domain,
        "pt_reduction": pt_reduction,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "The spectral shortcut is valid only with a sign-reversing PT action. "
            "Plain commutation is rejected because it does not pair lambda with -lambda."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Dirac-Cartan APS PT Reduction",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## Domain",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["domain"].items())
    lines.extend(["", "## PT Reduction"])
    lines.extend(f"- {key}: {value}" for key, value in payload["pt_reduction"].items())
    lines.extend(["", "## Status"])
    lines.extend(f"- {key}: {value}" for key, value in payload["theorem_status"].items())
    lines.extend(["", "## Obligations"])
    lines.extend(f"- {item}" for item in payload["obligations"])
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
