from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_map_integrability_curl_conditions.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_map_integrability_curl_conditions.json")


def build_payload() -> dict:
    map_equations = [
        {
            "id": "E_phi_plus",
            "sector": "plus",
            "equation": "J_phi_plus_nu := E_phi^A partial_nu phi_A + C_plus_nu[DeltaGamma(phi,L)] = 0",
            "cancels": "plus connection-difference residual in R_plus_nu",
            "curl_condition": "D_plus_[mu J_phi_plus_nu] = 0",
        },
        {
            "id": "E_L_plus",
            "sector": "plus",
            "equation": "J_L_plus_nu := E_L^{IJ} D_plus_nu L_{IJ} + S_plus_nu[Deltaomega(phi,L)] = 0",
            "cancels": "plus Lorentz connection-difference residual in R_plus_nu",
            "curl_condition": "D_plus_[mu J_L_plus_nu] = 0",
        },
        {
            "id": "E_phi_minus",
            "sector": "minus",
            "equation": "J_phi_minus_a := mirror(E_phi^A partial_a phi^{-1}_A) + C_minus_a[DeltaGamma(phi^{-1},L^{-1})] = 0",
            "cancels": "minus connection-difference residual in R_minus_a",
            "curl_condition": "D_minus_[a J_phi_minus_b] = 0",
        },
        {
            "id": "E_L_minus",
            "sector": "minus",
            "equation": "J_L_minus_a := mirror(E_L^{IJ} D_minus_a L^{-1}_{IJ}) + S_minus_a[Deltaomega(phi^{-1},L^{-1})] = 0",
            "cancels": "minus Lorentz connection-difference residual in R_minus_a",
            "curl_condition": "D_minus_[a J_L_minus_b] = 0",
        },
    ]
    curl_tests = [
        {
            "name": "phi_plus_frobenius",
            "operator": "D_plus_[mu D_plus_nu] phi_A",
            "expected_form": "curvature/torsion commutator plus curl C_plus[DeltaGamma]",
            "vanishes": "conditional",
            "obstruction": "R_plus acts on pulled map data unless source-derived identities cancel it",
        },
        {
            "name": "L_plus_frobenius",
            "operator": "D_plus_[mu D_plus_nu] L_{IJ}",
            "expected_form": "Lorentz curvature commutator plus curl S_plus[Deltaomega]",
            "vanishes": "conditional",
            "obstruction": "Omega_plus curvature acts on L unless matched by Deltaomega curl",
        },
        {
            "name": "phi_minus_frobenius",
            "operator": "D_minus_[a D_minus_b] phi^{-1}_A",
            "expected_form": "mirror curvature/torsion commutator plus curl C_minus[DeltaGamma]",
            "vanishes": "conditional",
            "obstruction": "R_minus mirror obstruction must be inverse of plus obstruction",
        },
        {
            "name": "L_minus_frobenius",
            "operator": "D_minus_[a D_minus_b] L^{-1}_{IJ}",
            "expected_form": "mirror Lorentz curvature commutator plus curl S_minus[Deltaomega]",
            "vanishes": "conditional",
            "obstruction": "Omega_minus mirror obstruction must be inverse of plus obstruction",
        },
    ]
    consistency_conditions = [
        {
            "name": "frobenius_like_closure",
            "condition": "the one-forms J_phi and J_L must be curl-free on the image distribution",
            "status": "required-not-proved",
        },
        {
            "name": "curvature_obstruction",
            "condition": "commutators [D,D]phi and [D,D]L must be cancelled by curls of DeltaGamma/Deltaomega terms",
            "status": "open-obstruction",
        },
        {
            "name": "mirror_consistency",
            "condition": "minus curl conditions are phi^{-1}, L^{-1} mirrors of plus curl conditions, not independent fits",
            "status": "required-not-proved",
        },
        {
            "name": "no_fit",
            "condition": "all curls use phi, L, g_plus, g_minus and source tensors only; no fitted curl source",
            "status": "enforced-by-branch",
        },
    ]
    closure_decision = {
        "curls_vanish": "conditional",
        "curls_vanish_false_unconditionally": True,
        "integrability_closes": False,
        "conditional_closure_possible": True,
        "reason": (
            "The curls expose Frobenius-like commutators for E_phi and E_L. They do not "
            "vanish identically: curvature and Lorentz-curvature obstructions remain "
            "unless the same source-derived map equations cancel the DeltaGamma and "
            "Deltaomega curls in both mirror sectors."
        ),
        "required_for_closure": [
            "derive J_phi=0 and J_L=0 from one covariant action",
            "prove D[J_phi]=0 and D[J_L]=0 as source identities rather than gauge choices",
            "show curvature obstruction terms cancel without fit",
            "prove minus-sector curls are inverse mirrors of plus-sector curls",
        ],
    }
    return {
        "description": (
            "Bounded P0 artifact deriving integrability curl conditions for Stueckelberg "
            "E_phi/E_L map equations that cancel connection differences."
        ),
        "status": "map-integrability-curl-conditional-open",
        "source_derived": False,
        "new_axiom": True,
        "physics_closed": False,
        "prediction_ready": False,
        "fit_to_observations": False,
        "free_parameters": [],
        "map_equations": map_equations,
        "curl_tests": curl_tests,
        "consistency_conditions": consistency_conditions,
        "closure_decision": closure_decision,
        "verdict": (
            "The curl conditions are necessary integrability gates for the Stueckelberg "
            "map-equation cancellation route. They are not a closure proof: curls vanish "
            "only conditionally, with curvature obstruction and mirror consistency still "
            "blocking prediction readiness."
        ),
    }


def render_markdown(payload: dict) -> str:
    decision = payload["closure_decision"]
    lines = [
        "# P0 Stueckelberg Map Integrability Curl Conditions",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Source derived: {payload['source_derived']}",
        f"New axiom: {payload['new_axiom']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        f"Fit to observations: {payload['fit_to_observations']}",
        f"Free parameters: {payload['free_parameters']}",
        "",
        "## Map Equations And Curls",
        "",
    ]
    for row in payload["map_equations"]:
        lines.append(f"- {row['id']} ({row['sector']}): `{row['equation']}`")
        lines.append(f"  - cancels: {row['cancels']}")
        lines.append(f"  - curl condition: `{row['curl_condition']}`")
    lines.extend(["", "## Curl Tests", ""])
    for row in payload["curl_tests"]:
        lines.append(f"- {row['name']}: `{row['operator']}`")
        lines.append(f"  - expected form: {row['expected_form']}")
        lines.append(f"  - vanishes: {row['vanishes']}")
        lines.append(f"  - obstruction: {row['obstruction']}")
    lines.extend(["", "## Consistency Conditions", ""])
    for row in payload["consistency_conditions"]:
        lines.append(f"- {row['name']}: {row['condition']} (status={row['status']})")
    lines.extend(
        [
            "",
            "## Closure Decision",
            "",
            f"Curls vanish: {decision['curls_vanish']}",
            f"Curls vanish false unconditionally: {decision['curls_vanish_false_unconditionally']}",
            f"Integrability closes: {decision['integrability_closes']}",
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
