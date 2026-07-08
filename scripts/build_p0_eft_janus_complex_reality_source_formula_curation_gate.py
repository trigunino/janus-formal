from __future__ import annotations

import json
from pathlib import Path
from typing import Any


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_complex_reality_source_formula_curation_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_complex_reality_source_formula_curation_gate.md"


def build_payload() -> dict[str, Any]:
    anchors = [
        {
            "id": "complex_hermite_metric",
            "pages": [16, 17],
            "equations": ["84", "85", "86", "87", "90", "92", "93"],
            "content": "Complex coordinates use adjoint/conjugation; the complexified Minkowski metric is ds2 = dX_dagger G dX.",
            "usable_for_state_law": True,
        },
        {
            "id": "complex_lorentz_poincare_group",
            "pages": [17],
            "equations": ["97", "98"],
            "content": "Complex Lorentz/Poincare condition: L_dagger G L = G, with group element (L,C;0,1).",
            "usable_for_state_law": True,
        },
        {
            "id": "complex_lie_algebra_action",
            "pages": [17, 18],
            "equations": ["103", "106", "107", "108", "109", "110"],
            "content": "Lie algebra element Z = (G omega, gamma; 0,0), with omega anti-Hermitian, and adjoint action omega_prime = L_dagger omega L.",
            "usable_for_state_law": True,
        },
        {
            "id": "complex_moment_space",
            "pages": [18, 19],
            "equations": ["111", "112", "113", "118"],
            "content": "Moment is mu = {M,P}; M is anti-Hermitian and P is a complex four-vector.",
            "usable_for_state_law": True,
        },
        {
            "id": "complex_duality_pairing",
            "pages": [19],
            "equations": ["114", "119", "120", "121"],
            "content": "Duality pairing is 1/2 Tr(M omega) + P_dagger G gamma.",
            "usable_for_state_law": True,
        },
        {
            "id": "complex_coadjoint_action",
            "pages": [19, 20],
            "equations": ["122", "123", "124", "128", "129", "130", "131", "132"],
            "content": "The document derives P = L P_prime and a complex coadjoint action written as mu_prime = a mu a_dagger.",
            "usable_for_state_law": True,
            "caveat": "The translation term in Eq. 131 must be checked against anti-Hermitian projection; the real appendix uses an antisymmetrized subtraction.",
        },
        {
            "id": "real_appendix_antisymmetrized_translation_term",
            "pages": [21, 22, 23],
            "equations": ["appendix 1", "appendix 10", "appendix 13", "appendix 15"],
            "content": "The real coadjoint action keeps only the antisymmetric part of the translation term, yielding M = L M_prime L_t + C P_prime_t L_t - L P C_t.",
            "usable_for_state_law": True,
        },
        {
            "id": "t_symmetry_mass_sign",
            "pages": [14],
            "equations": ["78"],
            "content": "T-symmetry reverses energy and momentum; with E=mc2 this supports mass sign reversal.",
            "usable_for_state_law": True,
        },
        {
            "id": "compact_dimension_quantization_hint",
            "pages": [14, 15],
            "equations": [],
            "content": "The text links compact extra dimensions to charge conjugation and quantization, but does not compute a Janus alpha lattice.",
            "usable_for_state_law": "qualitative_only",
        },
    ]
    return {
        "status": "janus-complex-reality-source-formula-curation-gate",
        "source_anchor": "X2026-complex-reality",
        "curated_formula_anchors": anchors,
        "what_document_adds": {
            "complex_coadjoint_state_space": True,
            "complex_moment_pair_M_P": True,
            "complex_souriau_pairing": True,
            "PT_mass_sign_support": True,
            "geometric_quantization_motivation": True,
        },
        "what_document_does_not_yet_add": {
            "boundary_phase_space_on_Sigma": True,
            "nonzero_KKS_boundary_density": True,
            "integrality_periods": True,
            "mass_or_charge_lattice": True,
            "primitive_sector_selection": True,
            "alpha_fixed": True,
        },
        "state_law_impact": (
            "The document upgrades the previous Souriau route from a generic "
            "Poincare orbit idea to a concrete complex coadjoint-state scaffold. "
            "It still stops before the boundary symplectic density and "
            "prequantization theorem needed to fix alpha."
        ),
        "next_gate": "ComplexRealityCoadjointStateSpaceGate",
        "formula_curation_ready": True,
        "alpha_generated_now": False,
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Complex Reality Source Formula Curation Gate",
                "",
                f"Source anchor: `{payload['source_anchor']}`",
                f"Formula curation ready: `{payload['formula_curation_ready']}`",
                f"Alpha generated now: `{payload['alpha_generated_now']}`",
                f"Next gate: `{payload['next_gate']}`",
                "",
                "## What The Document Adds",
                "",
                *[
                    f"- `{key}`: `{value}`"
                    for key, value in payload["what_document_adds"].items()
                ],
                "",
                "## Remaining Missing Pieces",
                "",
                *[
                    f"- `{key}`: `{value}`"
                    for key, value in payload["what_document_does_not_yet_add"].items()
                ],
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
