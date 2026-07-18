from __future__ import annotations

import json
from pathlib import Path

from scripts.audit_janus_worldvolume_microscopic_manifest import (
    DEFAULT_MANIFEST,
    audit_manifest,
    load_and_audit,
)


def test_repository_manifest_is_consistent_but_total_rg_waits_on_ll() -> None:
    audit = load_and_audit(DEFAULT_MANIFEST)
    assert audit.representation_consistent
    assert audit.compact_u1_fixed
    assert audit.paired_pt_levels_consistent
    assert audit.interaction_basis_present
    assert audit.effective_action_projection_fixed
    assert audit.non_ll_perturbative_ready
    assert not audit.ll_quantum_completion_fixed
    assert audit.logarithmic_residue_scheme_fixed
    assert audit.physical_matching_scheme_fixed
    assert audit.cross_scheme_covariance_derived
    assert audit.conditional_non_ll_results_recorded
    assert audit.program_p_ll_bridge_available
    assert not audit.cross_scheme_matching_complete
    assert not audit.perturbative_rg_ready
    assert audit.missing_rg_choices == (
        "cross_scheme_matching",
        "ll_quantum_completion",
    )
    assert audit.verdict == "ready_for_non_ll_calculation_blocked_on_ll_completion"


def test_charged_one_component_real_scalar_is_rejected() -> None:
    payload = json.loads(Path(DEFAULT_MANIFEST).read_text(encoding="utf-8"))
    payload["scalar"]["u1_charge"] = 1
    assert not audit_manifest(payload).representation_consistent


def test_missing_regulator_blocks_candidate() -> None:
    payload = json.loads(Path(DEFAULT_MANIFEST).read_text(encoding="utf-8"))
    payload["regulator"] = "not_yet_fixed"
    assert not audit_manifest(payload).perturbative_rg_ready


def test_missing_effective_action_projection_blocks_candidate() -> None:
    payload = json.loads(Path(DEFAULT_MANIFEST).read_text(encoding="utf-8"))
    del payload["perturbative_background"]["effective_action_projection"]
    assert not audit_manifest(payload).effective_action_projection_fixed
    assert not audit_manifest(payload).perturbative_rg_ready
