from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_m30_bulk_to_sigma_distribution_reduction.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_m30_bulk_to_sigma_distribution_reduction.json"
)


def build_payload() -> dict:
    formulae = {
        "m30_interaction_action": (
            "A_int = int_{M+} mu_+ Sbar_+ + int_{M-} mu_- S_-"
        ),
        "collar_split": (
            "M = M_+ union_Sigma M_- with signed normal coordinate n and throat embedding X_Sigma"
        ),
        "normal_embedding_variation": "delta X_Sigma = xi n",
        "bulk_to_boundary_variation": (
            "delta_X A_int|Sigma = int_Sigma xi [i_n(mu_+ Sbar_+) - i_n(mu_- S_-)]"
        ),
        "surface_force_density": (
            "F_Sigma = sqrt|h| (N_+ Sbar_+|Sigma - N_- S_-|Sigma)"
        ),
        "counterterm_condition": (
            "delta_R S_ct = -int_Sigma delta R_Sigma F_Sigma"
        ),
        "primitive_if_force_known": (
            "L_ct(R) = - integral^R F_Sigma(R')/sqrt|h(R')| dR' + Z2-allowed constant"
        ),
    }
    required_inputs = {
        "active_embedding_X_pm": False,
        "normal_lapses_N_pm_on_Sigma": False,
        "interaction_scalars_Sbar_plus_S_minus_on_Sigma": False,
        "determinant_ratio_bridge_on_Sigma": False,
        "Z2_parity_of_interaction_scalars": False,
        "bulk_EOM_or_Bianchi_terms_removed": False,
    }
    derived = {
        "normal_variation_formula_derived": True,
        "M30_interaction_can_source_sigma_force_conditionally": True,
        "explicit_counterterm_density_derived": False,
        "sigma_reduction_closed": False,
        "can_feed_R_h_R_K_R_chi": False,
    }
    blockers = [key for key, ready in required_inputs.items() if not ready]
    return {
        "status": "janus-z2-sigma-m30-bulk-to-sigma-distribution-reduction",
        "active_core": "Z2_tunnel_Sigma",
        "derivation_kind": "normal_variation_of_bulk_interaction_action_cut_by_sigma",
        "formulae": formulae,
        "required_inputs": required_inputs,
        "derived": derived,
        "gate_passed": False,
        "primary_blocker": blockers[0],
        "blockers": blockers,
        "bibliography": [
            {
                "id": "M30",
                "url": "https://arxiv.org/pdf/2412.04644v3",
                "role": "two-layer Janus interaction action and interaction tensors",
            },
            {
                "id": "M15",
                "url": "https://januscosmologicalmodel.com/pdf/2015-AstrophysSpaceSci.pdf",
                "role": "Janus constrained bivariation delta g_plus = - delta g_minus",
            },
            {
                "id": "Brown-York",
                "url": "https://arxiv.org/abs/gr-qc/9209012",
                "role": "boundary stress from action variation",
            },
            {
                "id": "Einstein-Cartan thin shells",
                "url": "https://arxiv.org/abs/2006.04044",
                "role": "torsion-compatible shell junction structure",
            },
        ],
        "next_required": [
            "derive or write active embedding X_+/X_- and normal lapses N_+/N_- on Sigma",
            "extract M30 interaction scalar densities Sbar_+ and S_- on Sigma",
            "prove their Z2 parity under projective throat gluing",
            "then integrate F_Sigma to obtain L_ct(R_Sigma)",
        ],
        "verdict": (
            "The mathematically correct route is a normal-variation reduction of the "
            "M30 bulk interaction action cut by Sigma. This yields a conditional "
            "surface force formula, not a closed counterterm. Closure now requires "
            "active embedding, normal lapse, and interaction scalar data on Sigma."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Janus Z2/Sigma M30 Bulk-to-Sigma Distribution Reduction",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        payload["verdict"],
        "",
        "## Formulae",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["formulae"].items())
    lines.extend(["", "## Required Inputs"])
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["required_inputs"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    return "\n".join(lines)


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(render_markdown(payload), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
