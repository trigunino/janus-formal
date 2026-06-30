from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_projected_dust_variation_identity.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_projected_dust_variation_identity.json")


def build_payload() -> dict:
    identity_chain = [
        {
            "step": "matter_map_variation",
            "identity": "delta S_dust = -int sqrt|g| (nabla_mu T^{mu}_{nu}) xi^nu",
            "status": "standard-diffeomorphism-identity",
        },
        {
            "step": "dust_stress",
            "identity": "T^{mu nu}=rho u^mu u^nu",
            "status": "dust-assumption",
        },
        {
            "step": "divergence_split",
            "identity": "nabla_mu T^{mu}_{nu}=u_nu nabla_mu(rho u^mu)+rho u^mu nabla_mu u_nu",
            "status": "algebraic",
        },
        {
            "step": "transverse_projection",
            "identity": "h^nu_sigma nabla_mu T^{mu}_{nu}=rho h^nu_sigma u^mu nabla_mu u_nu",
            "status": "conditional-on-normalized-dust",
        },
        {
            "step": "transported_connection_residual",
            "identity": "h a_to = h C u u when source dust is geodesic before transport",
            "status": "conditional-on-phi/L-transport",
        },
    ]
    sector_targets = [
        {
            "sector": "plus",
            "target": "h_plus^sigma_mu E_phi/L^mu = rho_minus_to_plus h_plus^sigma_mu C_plus-minus^mu_{alpha beta} u_-to+^alpha u_-to+^beta",
            "closed": "conditional",
        },
        {
            "sector": "minus",
            "target": "h_minus^c_a E_phi/L^a = rho_plus_to_minus h_minus^c_a C_minus-plus^a_{mu nu} u_+to-^mu u_+to-^nu",
            "closed": "conditional",
        },
    ]
    obligations = [
        "the pulled dust action must be a true diffeomorphism pullback/pushforward, not an ad hoc scalar copy",
        "density Jacobian and volume conventions must match the D_phi/DlogB artifacts",
        "the same phi/L must define K_plus, K_minus, and Q_cross",
        "mirror sector identity must be the inverse-map counterpart, not separately imposed",
        "pressure and anisotropic stress require a separate perfect-fluid/Pi extension",
    ]
    decision = {
        "projected_identity_found": True,
        "new_multiplier_needed": False,
        "dust_connection_residual_closed": "conditional",
        "full_matter_closed": False,
        "source_derived_from_standard_matter_variation": True,
        "janus_specific_action_still_required": True,
        "prediction_ready": False,
        "reason": (
            "For dust, the transverse projected map variation has the right no-new-field "
            "shape: it is the transverse divergence of transported dust stress. This can "
            "supply rho h Cuu conditionally, but only after the Janus pulled-action and "
            "mirror conventions are fixed consistently."
        ),
    }
    return {
        "artifact": "p0_stueckelberg_projected_dust_variation_identity",
        "status": "projected-dust-identity-conditional-progress",
        "fit_used": False,
        "free_parameters": [],
        "physics_closed": False,
        "prediction_ready": False,
        "identity_chain": identity_chain,
        "sector_targets": sector_targets,
        "closure_obligations": obligations,
        "decision": decision,
    }


def render_markdown(payload: dict) -> str:
    decision = payload["decision"]
    lines = [
        "# P0 Stueckelberg Projected Dust Variation Identity",
        "",
        f"Status: {payload['status']}",
        f"Fit used: {payload['fit_used']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Identity Chain",
    ]
    for row in payload["identity_chain"]:
        lines.append(f"- {row['step']}: `{row['identity']}` ({row['status']})")
    lines.extend(["", "## Sector Targets"])
    for row in payload["sector_targets"]:
        lines.append(f"- {row['sector']}: `{row['target']}`; closed={row['closed']}")
    lines.extend(["", "## Closure Obligations"])
    lines.extend(f"- {item}" for item in payload["closure_obligations"])
    lines.extend(
        [
            "",
            "## Decision",
            f"Projected identity found: {decision['projected_identity_found']}",
            f"New multiplier needed: {decision['new_multiplier_needed']}",
            f"Dust connection residual closed: {decision['dust_connection_residual_closed']}",
            f"Full matter closed: {decision['full_matter_closed']}",
            f"Source derived from standard matter variation: {decision['source_derived_from_standard_matter_variation']}",
            f"Janus specific action still required: {decision['janus_specific_action_still_required']}",
            f"Reason: {decision['reason']}",
            "",
        ]
    )
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    payload = build_payload()
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    return payload


if __name__ == "__main__":
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")
