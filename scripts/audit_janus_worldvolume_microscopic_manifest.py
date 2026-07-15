from __future__ import annotations

import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


DEFAULT_MANIFEST = Path("data/worldvolume_quantum_candidate_manifest.json")


@dataclass(frozen=True)
class ManifestAudit:
    representation_consistent: bool
    compact_u1_fixed: bool
    paired_pt_levels_consistent: bool
    interaction_basis_present: bool
    effective_action_projection_fixed: bool
    non_ll_perturbative_ready: bool
    ll_quantum_completion_fixed: bool
    logarithmic_residue_scheme_fixed: bool
    physical_matching_scheme_fixed: bool
    cross_scheme_matching_complete: bool
    cross_scheme_covariance_derived: bool
    conditional_non_ll_results_recorded: bool
    perturbative_rg_ready: bool
    missing_rg_choices: tuple[str, ...]
    verdict: str


def audit_manifest(payload: dict[str, Any]) -> ManifestAudit:
    scalar = payload.get("scalar", {})
    cs = payload.get("chern_simons", {})
    interactions = set(payload.get("interactions", []))
    representation_ok = not (
        scalar.get("kind") == "real"
        and scalar.get("multiplicity") == 1
        and scalar.get("u1_charge") != 0
    )
    compact_u1 = payload.get("gauge_group") == "U(1)" and bool(
        payload.get("gauge_group_compact")
    )
    paired_levels = (
        bool(cs.get("paired_pt"))
        and isinstance(cs.get("level_plus"), int)
        and isinstance(cs.get("level_minus"), int)
        and cs.get("level_plus") == -cs.get("level_minus")
    )
    required_interactions = {
        "scalar_kinetic",
        "scalar_sextic",
        "scalar_dressed_maxwell",
        "gauge_chern_simons",
        "ll_non_riemannian_measure",
    }
    basis_present = required_interactions <= interactions
    background = payload.get("perturbative_background", {})
    background_ready = (
        background.get("scalar_condensate_nonzero") is True
        and background.get("field_split") == "phi=v+eta"
        and isinstance(background.get("dressed_maxwell_expansion_order"), int)
        and background.get("dressed_maxwell_expansion_order") >= 6
    )
    projection_fixed = (
        background.get("effective_action_projection")
        == "constant_scalar_background_potential"
        and background.get("maximum_external_derivative_order") == 0
    )
    rg_keys = ("gauge_fixing", "regulator", "subtraction_scheme", "loop_order")
    missing = tuple(
        key for key in rg_keys if payload.get(key) in (None, "not_yet_fixed")
    )
    if not background_ready:
        missing = (*missing, "perturbative_background")
    if not projection_fixed:
        missing = (*missing, "effective_action_projection")
    non_ll_ready = representation_ok and compact_u1 and paired_levels and basis_present and not missing
    ll_completion = payload.get("ll_quantum_completion", {})
    prescriptions = payload.get("renormalization_prescriptions", {})
    log_prescription = prescriptions.get("logarithmic_residues", {})
    physical_prescription = prescriptions.get("finite_physical_matching", {})
    log_scheme_fixed = (
        log_prescription.get("regulator")
        == "dimensional_regularization_d_3_minus_2epsilon"
        and log_prescription.get("subtraction") == "minimal_subtraction"
    )
    physical_scheme_fixed = (
        physical_prescription.get("regulator")
        == payload.get("regulator")
        and physical_prescription.get("subtraction")
        == payload.get("subtraction_scheme")
    )
    cross_scheme = prescriptions.get("cross_scheme_matching", {})
    cross_scheme_covariance = (
        cross_scheme.get("one_log_covariance") == "derived"
        and cross_scheme.get("leading_beta_invariance") == "derived"
    )
    cross_scheme_complete = (
        cross_scheme_covariance
        and cross_scheme.get("finite_matching_constant")
        not in (None, "not_yet_computed")
    )
    if not log_scheme_fixed:
        missing = (*missing, "logarithmic_residue_scheme")
    if not physical_scheme_fixed:
        missing = (*missing, "physical_matching_scheme")
    if not cross_scheme_complete:
        missing = (*missing, "cross_scheme_matching")
    conditional_results = payload.get("conditional_ms_results", {})
    non_ll_results_recorded = conditional_results == {
        "pure_scalar_beta_quadratic_coefficient": "25/(2*pi^2)",
        "mixed_beta_quadratic_coefficient": "75/(32*pi^2)",
        "non_ll_beta_quadratic_coefficient": "475/(32*pi^2)",
        "one_loop_non_ll_anomalous_dimension": "0",
        "two_loop_non_ll_composite_anomalous_coefficient": "5/(16*pi^2)",
        "non_ll_callan_symanzik_quadratic_coefficient": "445/(32*pi^2)",
    }
    if not non_ll_results_recorded:
        missing = (*missing, "conditional_ms_results")
    ll_keys = (
        "local_measure_fields",
        "reducibility_tower",
        "gauge_fermion",
        "fp_bv_operator",
        "zero_mode_prescription",
    )
    ll_fixed = all(ll_completion.get(key) not in (None, "not_yet_fixed") for key in ll_keys)
    if not ll_fixed:
        missing = (*missing, "ll_quantum_completion")
    ready = non_ll_ready and ll_fixed
    return ManifestAudit(
        representation_consistent=representation_ok,
        compact_u1_fixed=compact_u1,
        paired_pt_levels_consistent=paired_levels,
        interaction_basis_present=basis_present,
        effective_action_projection_fixed=projection_fixed,
        non_ll_perturbative_ready=non_ll_ready,
        ll_quantum_completion_fixed=ll_fixed,
        logarithmic_residue_scheme_fixed=log_scheme_fixed,
        physical_matching_scheme_fixed=physical_scheme_fixed,
        cross_scheme_matching_complete=cross_scheme_complete,
        cross_scheme_covariance_derived=cross_scheme_covariance,
        conditional_non_ll_results_recorded=non_ll_results_recorded,
        perturbative_rg_ready=ready,
        missing_rg_choices=missing,
        verdict=(
            "ready_for_total_conditional_loop_calculation"
            if ready
            else (
                "ready_for_non_ll_calculation_blocked_on_ll_completion"
                if non_ll_ready and not ll_fixed
                else "candidate_manifest_incomplete"
            )
        ),
    )


def load_and_audit(path: Path = DEFAULT_MANIFEST) -> ManifestAudit:
    return audit_manifest(json.loads(path.read_text(encoding="utf-8")))


def main() -> int:
    print(json.dumps(asdict(load_and_audit()), indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
