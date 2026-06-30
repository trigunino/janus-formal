from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_map_equation_connection_compatibility.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_map_equation_connection_compatibility.json")


def build_payload() -> dict:
    compatibility_equations = [
        {
            "id": "E_phi_plus",
            "sector": "plus",
            "equation": "E_phi^A partial_nu phi_A = -C_plus_nu[DeltaGamma(phi,L)]",
            "role": "cancel the pullback connection-difference term in R_plus_nu",
        },
        {
            "id": "E_L_plus",
            "sector": "plus",
            "equation": "E_L^{IJ} D_plus_nu L_{IJ} = -S_plus_nu[Deltaomega(phi,L)]",
            "role": "cancel the pushed Lorentz-frame connection-difference term in R_plus_nu",
        },
        {
            "id": "E_phi_minus",
            "sector": "minus",
            "equation": "mirror(E_phi^A partial_a phi_A) = -C_minus_a[DeltaGamma(phi^{-1},L^{-1})]",
            "role": "cancel the pushforward connection-difference term in R_minus_a",
        },
        {
            "id": "E_L_minus",
            "sector": "minus",
            "equation": "E_L^{IJ} D_minus_a L^{-1}_{IJ} = -S_minus_a[Deltaomega(phi^{-1},L^{-1})]",
            "role": "cancel the mirror Lorentz-frame connection-difference term in R_minus_a",
        },
    ]
    checks = [
        {
            "name": "integrability",
            "requirement": "curl(E_phi partial phi + C[DeltaGamma])=0 and curl(E_L D L + S[Deltaomega])=0",
            "status": "open",
        },
        {
            "name": "overconstraint",
            "requirement": "count independent plus/minus cancellation equations against phi and L gauge freedom",
            "status": "likely-overconstrained",
        },
        {
            "name": "mirror_sector_consistency",
            "requirement": "minus equations are the phi^{-1}, L^{-1} mirror of plus equations with no independent map",
            "status": "required-not-proved",
        },
        {
            "name": "no_fit",
            "requirement": "all connection differences are computed from phi, L, g_plus, and g_minus; no fitted amplitudes",
            "status": "enforced-by-branch",
        },
    ]
    closure_decision = {
        "compatibility_closes": False,
        "conditional_closure_possible": True,
        "reason": (
            "The equations state what E_phi and E_L would need to cancel in both residuals, "
            "but integrability and independent-equation counting are not derived from the "
            "source model."
        ),
        "required_for_closure": [
            "derive the four cancellation equations from one covariant action",
            "prove the integrability curls vanish or are source-derived identities",
            "show the plus and minus equations are mirror images, not separate fits",
            "show the phi/L unknowns are not overconstrained by both residuals",
        ],
    }
    return {
        "description": (
            "Bounded P0 artifact for Stueckelberg map-equation compatibility with "
            "connection-difference residual terms."
        ),
        "status": "connection-compatibility-conditional-open",
        "source_derived": False,
        "new_axiom": True,
        "physics_closed": False,
        "prediction_ready": False,
        "fit_to_observations": False,
        "connection_difference_terms": ["DeltaGamma(phi,L)", "Deltaomega(phi,L)"],
        "compatibility_equations": compatibility_equations,
        "checks": checks,
        "closure_decision": closure_decision,
        "verdict": (
            "This formulates the needed E_phi/E_L cancellation conditions. It is not a "
            "closure proof: the branch remains conditional and prediction-blocked until "
            "integrability, mirror consistency, and overconstraint checks close without fit."
        ),
    }


def render_markdown(payload: dict) -> str:
    decision = payload["closure_decision"]
    lines = [
        "# P0 Stueckelberg Map Equation Connection Compatibility",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Source derived: {payload['source_derived']}",
        f"New axiom: {payload['new_axiom']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        f"Fit to observations: {payload['fit_to_observations']}",
        "",
        "## Connection Differences",
        "",
    ]
    lines.extend(f"- `{term}`" for term in payload["connection_difference_terms"])
    lines.extend(["", "## Compatibility Equations", ""])
    for row in payload["compatibility_equations"]:
        lines.append(f"- {row['id']} ({row['sector']}): `{row['equation']}`; {row['role']}")
    lines.extend(["", "## Checks", ""])
    for row in payload["checks"]:
        lines.append(f"- {row['name']}: {row['requirement']} (status={row['status']})")
    lines.extend(
        [
            "",
            "## Closure Decision",
            "",
            f"Compatibility closes: {decision['compatibility_closes']}",
            f"Conditional closure possible: {decision['conditional_closure_possible']}",
            f"Reason: {decision['reason']}",
            "",
            "## Required For Closure",
            "",
        ]
    )
    lines.extend(f"- {item}" for item in decision["required_for_closure"])
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
