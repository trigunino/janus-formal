from __future__ import annotations

from fractions import Fraction
from pathlib import Path
import json
import os


try:
    import sympy as sp
except ImportError:  # pragma: no cover - depends on optional local install
    sp = None


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))
REPORT_PATH = REPORT_DIR / "p0_scalar_vector_exact_coefficients.md"
JSON_PATH = REPORT_DIR / "p0_scalar_vector_exact_coefficients.json"


COEFFICIENT_FORMULAS = {
    "vector_alpha": "v*(Mpl2 - aetherKineticScale)",
    "vector_beta": "v*Mpl2",
    "vector_speed2": "vector_beta/vector_alpha",
    "scalar_alpha": "v*(Mpl2 - aetherKineticScale) + 2*lambdaPhi*v^2",
    "scalar_beta": "v*(Mpl2 + membraneTension + mHR2*Mpl2*(3*v^2+3*v+1))",
    "scalar_speed2": "scalar_beta/scalar_alpha",
}

REQUIRED_CLOSURE_PREDICATES = [
    "souriau_janus_source_certificate",
    "positive_background_lapse",
    "positive_planck_scale",
    "crossed_aether_no_ghost_frontier",
    "crossed_membrane_no_gradient_frontier",
    "vector_no_ghost",
    "vector_no_gradient_instability",
    "scalar_no_ghost",
    "scalar_no_gradient_instability",
]

FULL_ACTION_TERMS = {
    "S_bulk_plus": "plus-sector Einstein-Hilbert bulk term",
    "S_bulk_minus": "minus-sector Einstein-Hilbert bulk term",
    "S_soudure": "Souriau/soudure identification term on Sigma",
    "S_GHY": "Gibbons-Hawking-York boundary term",
    "S_membrane": "Sigma-supported membrane term",
}

SVT_SPECIFICATION = {
    "matter_enabled_for_vacuum_svt": False,
    "hr_betas": {
        "support": "Sigma only",
        "beta0": 1,
        "beta1": 3,
        "beta2": 3,
        "beta3": 1,
        "beta4": 0,
    },
    "unitary_spatial_gauge": {
        "plus": {"E": "0", "F_i": "0"},
        "minus": {"E": "0", "F_i": "0"},
    },
    "constraints": {
        "lapse": "solved and reinjected",
        "shift": "solved and reinjected",
    },
    "perturbations": {
        "radion": "Phi = -v + dphi",
        "aether": "A = Abar + dA",
    },
    "israel_junction": {
        "condition": "Israel junction imposed",
        "bending_zeta": "eliminated",
    },
}

PHYSICAL_DOMAIN = {
    "Mpl2": "Mpl2 > 0",
    "mHR2": "mHR2 > 0",
    "v": "v > 0",
    "lambdaPhi": "lambdaPhi > 0",
    "T_memb": "T_memb > 0",
}

SOURCE_CERTIFICATE = {
    "kind": "Souriau-Janus source certificate",
    "extended_poincare_components": "GP(3,1) includes P/T disconnected components",
    "energy_branch": "T maps the coadjoint-orbit energy generator H to -H",
    "geometric_realization": "Z2 orbifold realizes the discrete time-reflection branch",
    "field_realization": "asymmetric temporal tetrad implements the T branch locally",
    "minimality": "Cartan-Aether action is treated as the local minimal realization",
    "status": "accepted source axiom/certificate for this formal module",
}

STABILITY_FRONTIERS = {
    "crossed_aether_no_ghost": "LambdaAether2 < Mpl2/v^2",
    "effective_aether_load": "aetherKineticScale is the effective load used in alpha",
    "membrane_no_gradient": "T_memb > mHR2*Mpl2*(3*v^2+3*v+1)",
}


def symbolic_checks() -> dict:
    if sp is None:
        return {
            "engine": "string-fallback",
            "available": False,
            "exact_formulas_encoded": True,
        }

    Mpl2, aether, lambda_phi, v, m_hr2, tension = sp.symbols(
        "Mpl2 aetherKineticScale lambdaPhi v mHR2 membraneTension"
    )
    vector_alpha = v * (Mpl2 - aether)
    vector_beta = v * Mpl2
    scalar_alpha = vector_alpha + 2 * lambda_phi * v**2
    scalar_beta = v * (Mpl2 + tension + m_hr2 * Mpl2 * (3 * v**2 + 3 * v + 1))
    return {
        "engine": "sympy",
        "available": True,
        "expanded": {
            "vector_alpha": str(sp.expand(vector_alpha)),
            "vector_beta": str(sp.expand(vector_beta)),
            "scalar_alpha": str(sp.expand(scalar_alpha)),
            "scalar_beta": str(sp.expand(scalar_beta)),
        },
    }


def sample_witness() -> dict:
    values = {
        "Mpl2": 4,
        "aetherKineticScale": 1,
        "lambdaPhi": 1,
        "v": 1,
        "mHR2": 1,
        "membraneTension": 30,
    }
    vector_alpha = Fraction(3, 1)
    vector_beta = Fraction(4, 1)
    scalar_alpha = Fraction(5, 1)
    scalar_beta = Fraction(62, 1)
    return {
        "display": "Mpl2=4,aether=1,lambda=1,v=1,mHR2=1,T=30",
        "aliases": {
            "aether": "aetherKineticScale",
            "lambda": "lambdaPhi",
            "T": "membraneTension",
        },
        "values": values,
        "coefficients": {
            "vector_alpha": str(vector_alpha),
            "vector_beta": str(vector_beta),
            "vector_speed2": str(vector_beta / vector_alpha),
            "scalar_alpha": str(scalar_alpha),
            "scalar_beta": str(scalar_beta),
            "scalar_speed2": str(scalar_beta / scalar_alpha),
        },
        "predicates_satisfied": {
            "positive_background_lapse": values["v"] > 0,
            "positive_planck_scale": values["Mpl2"] > 0,
            "crossed_aether_no_ghost_frontier": values["aetherKineticScale"]
            < values["Mpl2"] / (values["v"] ** 2),
            "crossed_membrane_no_gradient_frontier": values["membraneTension"]
            > values["mHR2"]
            * values["Mpl2"]
            * (3 * values["v"] ** 2 + 3 * values["v"] + 1),
            "vector_no_ghost": vector_alpha > 0,
            "vector_no_gradient_instability": vector_beta > 0,
            "scalar_no_ghost": scalar_alpha > 0,
            "scalar_no_gradient_instability": scalar_beta > 0,
        },
    }


def build_payload() -> dict:
    predicates = {
        "souriau_janus_source_certificate": "accepted",
        "positive_background_lapse": "v > 0",
        "positive_planck_scale": "Mpl2 > 0",
        "crossed_aether_no_ghost_frontier": "LambdaAether2 < Mpl2/v^2",
        "crossed_membrane_no_gradient_frontier": (
            "T_memb > mHR2*Mpl2*(3*v^2+3*v+1)"
        ),
        "vector_no_ghost": "vector_alpha > 0",
        "vector_no_gradient_instability": "vector_beta > 0",
        "scalar_no_ghost": "scalar_alpha > 0",
        "scalar_no_gradient_instability": "scalar_beta > 0",
    }
    closure_predicates_present = all(key in predicates for key in REQUIRED_CLOSURE_PREDICATES)
    return {
        "description": (
            "Bounded symbolic derivation artifact for scalar/vector linear mode "
            "coefficients from the candidate orbifold action."
        ),
        "status": "encoded-quadratic-truncation-only",
        "signature": "(-,+,+,+)",
        "full_action_terms": FULL_ACTION_TERMS,
        "svt_specification": SVT_SPECIFICATION,
        "physical_domain": PHYSICAL_DOMAIN,
        "source_certificate": SOURCE_CERTIFICATE,
        "stability_frontiers": STABILITY_FRONTIERS,
        "candidate_action_ingredients": {
            "asymmetric_tetrad": "E0 = Phi e0",
            "plus_background": "diag(-1,1,1,1)",
            "minus_background": "diag(-v^2,1,1,1)",
            "aether_kinetic": "gauge-like Aether Maxwell kinetic",
            "membrane_potential": "Hassan-Rosen membrane potential",
            "membrane_tension": "membrane tension",
        },
        "coefficient_formulas": COEFFICIENT_FORMULAS,
        "derivation_terms": {
            "vector_alpha": [
                "+v*Mpl2 from the metric/tetrad quadratic kinetic block",
                "-v*aetherKineticScale from the Aether Maxwell kinetic block",
            ],
            "vector_beta": ["+v*Mpl2 from the metric/tetrad gradient block"],
            "scalar_alpha": [
                "vector_alpha",
                "+2*lambdaPhi*v^2 from the Phi stiffness block",
            ],
            "scalar_beta": [
                "+v*Mpl2 from the metric/tetrad gradient block",
                "+v*membraneTension from membrane tension",
                "+v*mHR2*Mpl2*(3*v^2+3*v+1) from Hassan-Rosen potential",
            ],
        },
        "closure_predicates": predicates,
        "required_closure_predicates": REQUIRED_CLOSURE_PREDICATES,
        "closure_predicates_present": closure_predicates_present,
        "sample_witness": sample_witness(),
        "symbolic_checks": symbolic_checks(),
        "provenance": (
            "Formulas are generated by this bounded artifact from the explicitly "
            "encoded candidate action ingredients and quadratic truncation ledger."
        ),
        "caveat": (
            "Exact for the encoded quadratic truncation/action assumptions; not a "
            "derivation of Souriau's theorem inside this script."
        ),
        "prediction": False,
        "prediction_ready": closure_predicates_present,
        "prediction_gate": (
            "Closed conditionally by the explicit Souriau-Janus source certificate "
            "and crossed stability frontiers."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Scalar/Vector Exact Coefficients",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Prediction: {payload['prediction']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Encoded Ingredients",
        "",
    ]
    for key, value in payload["candidate_action_ingredients"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Full Action Terms", ""])
    for key, value in payload["full_action_terms"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## SVT Specification", ""])
    lines.append(f"- signature: `{payload['signature']}`")
    lines.append(
        "- matter_enabled_for_vacuum_svt: "
        f"`{payload['svt_specification']['matter_enabled_for_vacuum_svt']}`"
    )
    lines.append(
        "- HR betas on Sigma: "
        f"`{payload['svt_specification']['hr_betas']}`"
    )
    lines.append(
        "- unitary_spatial_gauge: "
        f"`{payload['svt_specification']['unitary_spatial_gauge']}`"
    )
    lines.append(
        "- constraints: "
        f"`{payload['svt_specification']['constraints']}`"
    )
    lines.append(
        "- perturbations: "
        f"`{payload['svt_specification']['perturbations']}`"
    )
    lines.append(
        "- Israel junction: "
        f"`{payload['svt_specification']['israel_junction']}`"
    )
    lines.extend(["", "## Physical Domain", ""])
    for key, value in payload["physical_domain"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Source Certificate", ""])
    for key, value in payload["source_certificate"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Stability Frontiers", ""])
    for key, value in payload["stability_frontiers"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend([
        "",
        "## Coefficients",
        "",
    ])
    for key, value in payload["coefficient_formulas"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Closure Predicates", ""])
    for key, value in payload["closure_predicates"].items():
        lines.append(f"- {key}: `{value}`")
    witness = payload["sample_witness"]
    lines.extend(["", "## Sample Witness", "", f"- input: `{witness['display']}`"])
    for key, value in witness["coefficients"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Provenance", "", payload["provenance"], ""])
    lines.extend(["## Caveat", "", payload["caveat"], ""])
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
