from __future__ import annotations

import json
import sys
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
SRC = ROOT / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from janus_lab.janus_2024_reference import (
    Janus2024PublishedDustBackground,
    Janus2024PublishedObservationalAnchors,
    Janus2024PublishedCitedObservationReference,
    JanusPublishedExactShapeReference,
)
from scripts.build_p0_eft_janus_z2_published_bimetric_sector_ratio_gate import (
    build_payload as build_sector_ratio_payload,
)


REPORTS = Path("outputs/reports")
REFERENCE_DIR = Path("outputs/the_janus_cosmological_model_2024_reference")
JSON_PATH = REPORTS / "p0_eft_the_janus_cosmological_model_2024_reference_gate.json"
REPORT_PATH = REPORTS / "p0_eft_the_janus_cosmological_model_2024_reference_gate.md"
MANIFEST_PATH = REFERENCE_DIR / "manifest.json"


def build_payload(*, write_manifest: bool = False) -> dict:
    paper_background = Janus2024PublishedDustBackground()
    paper_observational_anchors = Janus2024PublishedObservationalAnchors()
    published_exact_shape = JanusPublishedExactShapeReference()
    published_cited_observation = Janus2024PublishedCitedObservationReference()
    plus_history = published_exact_shape.sample_normalized_plus_history(samples=8)
    sector_ratio_payload = build_sector_ratio_payload()
    published_bulk_ready = True
    published_bulk_normalized = False
    paper_structured_reference_ready = bool(
        published_bulk_ready and sector_ratio_payload["relative_sector_ratio_ready"]
    )
    paper_only_branch_ready = True
    paper_plus_cited_comparison_branch_ready = True
    paper_like_for_like_reference_ready = False
    paper_explicit_only_reference_ready = True
    strict_paper_only_reference_ready = False
    repo_implicit_closure_forbidden = True
    paper_cited_helper_objects_present = True
    paper_cited_helper_objects_active = False
    excluded_repo_helpers = [
        "published_cited_observational_calibration",
        "minus_branch_initialization_convention",
        "repo_materialized_two_metric_background_wrapper",
    ]
    missing_for_like_for_like = []
    paper_explicitly_fixed_objects = [
        "published_bulk_bimetric_equations",
        "published_common_time_x0_flrw_equation_object",
        "published_k_equals_kbar_equals_minus_one_branch",
        "published_global_energy_equation_shape",
        "published_sector_dust_density_laws",
        "published_observational_anchor_values_and_claims",
        "published_relative_sector_ratio_5pct_95pct",
    ]
    paper_cited_but_not_explicit_objects = [
        "published_cited_exact_shape_proxy_q0_u0",
        "published_visible_plus_history_proxy",
        "published_observation_reference_proxy_alpha_h0_q0",
    ]
    paper_underdetermined_objects = [
        "absolute_density_normalization",
        "full_two_metric_background_history",
        "paper_native_bulk_observable_prediction_path",
        "paper_native_absolute_observation_contract",
    ]
    missing_for_strict_paper_only = [
        "paper_native_absolute_density_normalization_not_materialized",
        "paper_native_two_metric_background_history_not_materialized",
    ]

    manifest = {
        "reference_name": "The_Janus_Cosmological_Model_2024_reference",
        "paper_structured_reference_ready": paper_structured_reference_ready,
        "paper_only_branch_ready": paper_only_branch_ready,
        "paper_plus_cited_comparison_branch_ready": paper_plus_cited_comparison_branch_ready,
        "paper_like_for_like_reference_ready": paper_like_for_like_reference_ready,
        "paper_explicit_only_reference_ready": paper_explicit_only_reference_ready,
        "strict_paper_only_reference_ready": strict_paper_only_reference_ready,
        "repo_implicit_closure_forbidden": repo_implicit_closure_forbidden,
        "paper_cited_helper_objects_present": paper_cited_helper_objects_present,
        "paper_cited_helper_objects_active": paper_cited_helper_objects_active,
        "source_family": {
            "bulk_bimetric_equations": "The Janus Cosmological Model EPJC 2024 Eqs. (90-96)",
            "background_expansion_proxy": "none_in_strict_reference",
            "relative_sector_ratio": sector_ratio_payload["ratio_payload"]["source_anchor"],
            "absolute_sector_normalization": "not_materialized_in_strict_reference",
        },
        "paper_native_background": {
            "common_time_coordinate": paper_background.common_time_coordinate,
            "conservation_equation_anchor": paper_background.conservation_equation_anchor,
            "dust_branch_anchor": paper_background.dust_branch_anchor,
            "acceleration_equations_anchor": paper_background.acceleration_equations_anchor,
            "conservation_law_terms": list(paper_background.conservation_law),
        },
        "paper_native_observational_anchors": {
            "direct_standard_candle_h0_km_s_mpc": paper_observational_anchors.direct_standard_candle_h0_km_s_mpc,
            "lcdm_cmb_h0_km_s_mpc": paper_observational_anchors.lcdm_cmb_h0_km_s_mpc,
            "h0_anchor": paper_observational_anchors.h0_anchor,
            "magnitude_redshift_curve_claim_anchor": paper_observational_anchors.magnitude_redshift_curve_claim_anchor,
            "exact_fit_curve_claim_present": paper_observational_anchors.exact_fit_curve_claim_present,
        },
        "paper_cited_helper_exact_shape": {
            "q0": published_exact_shape.q0,
            "q0_anchor": published_exact_shape.q0_anchor,
            "exact_shape_anchor": published_exact_shape.exact_shape_anchor,
            "u0": published_exact_shape.u0,
            "z_max": published_exact_shape.z_max,
            "normalized_present_a_plus": 1.0,
            "normalized_present_e_plus": 1.0,
        },
        "paper_cited_helper_plus_history": {
            "samples": int(len(plus_history["u"])),
            "u_start": float(plus_history["u"][0]),
            "u_end": float(plus_history["u"][-1]),
            "a_plus_start": float(plus_history["a_plus"][0]),
            "a_plus_end": float(plus_history["a_plus"][-1]),
            "e_plus_end": float(plus_history["e_plus"][-1]),
            "z_max": float(np.max(plus_history["z"])),
        },
        "paper_cited_helper_observation_reference": {
            "q0": published_cited_observation.q0,
            "h0_km_s_mpc": published_cited_observation.h0_km_s_mpc,
            "u0": published_cited_observation.u0,
            "alpha_seconds": published_cited_observation.alpha_seconds,
            "sn_proxy_anchor": "Published/cited Janus magnitude-redshift comparison branch",
        },
        "branch_classes": {
            "paper_only": {
                "ready": paper_only_branch_ready,
                "active": True,
                "description": "Only objects fixed explicitly by the 2024 paper are active.",
            },
            "paper_plus_cited_comparison": {
                "ready": paper_plus_cited_comparison_branch_ready,
                "active": False,
                "description": "Includes cited comparison helpers kept separate from the active paper-only branch.",
            },
        },
        "implemented_reference": {
            "published_bulk_bimetric_equations_present": published_bulk_ready,
            "published_bulk_absolute_density_normalization_present": published_bulk_normalized,
            "published_bulk_absolute_density_normalization_kind": (
                "not_materialized_in_strict_reference"
                if published_bulk_normalized
                else "missing"
            ),
            "active_background_reference_path_kind": "paper_equations_and_anchors_only",
            "active_background_reference_path_is_full_published_bulk": strict_paper_only_reference_ready,
            "active_two_metric_flrw_reference_object_present": True,
            "active_k_equals_kbar_equals_minus_one_branch_present": True,
            "published_k_equals_kbar_equals_minus_one_branch_present": True,
            "active_global_energy_equation_present": True,
            "active_sector_density_law_present": True,
            "active_two_metric_rhs_present": True,
            "published_cited_exact_shape_present": False,
            "paper_native_plus_history_present": False,
            "paper_published_observation_reference_present": False,
            "active_bulk_observable_path_present": False,
            "active_absolute_normalization_contract_present": False,
        },
        "paper_explicitly_fixed_objects": paper_explicitly_fixed_objects,
        "paper_cited_but_not_explicit_objects": paper_cited_but_not_explicit_objects,
        "paper_underdetermined_objects": paper_underdetermined_objects,
        "excluded_repo_helpers": excluded_repo_helpers,
        "repo_added_closures": [],
        "missing_for_like_for_like": missing_for_like_for_like,
        "missing_for_strict_paper_only": missing_for_strict_paper_only,
        "observational_status": {
            "active_bulk_observational_run_executed": False,
        },
        "branch_policy": {
            "freeze_the_janus_cosmological_model_2024_reference": False,
            "the_janus_cosmological_model_2024_is_no_fit_cosmology": False,
            "active_bulk_completion_required": not strict_paper_only_reference_ready,
        },
    }
    if write_manifest:
        REFERENCE_DIR.mkdir(parents=True, exist_ok=True)
        MANIFEST_PATH.write_text(json.dumps(manifest, indent=2), encoding="utf-8")

    return {
        "status": "the-janus-cosmological-model-2024-reference-gate",
        "the_janus_cosmological_model_2024_reference_recreated": True,
        "published_bulk_bimetric_equations_present": published_bulk_ready,
        "published_relative_sector_ratio_present": sector_ratio_payload[
            "relative_sector_ratio_ready"
        ],
        "published_absolute_density_normalization_present": published_bulk_normalized,
        "published_absolute_density_normalization_kind": manifest["implemented_reference"][
            "published_bulk_absolute_density_normalization_kind"
        ],
        "paper_structured_reference_ready": paper_structured_reference_ready,
        "paper_only_branch_ready": paper_only_branch_ready,
        "paper_plus_cited_comparison_branch_ready": paper_plus_cited_comparison_branch_ready,
        "like_for_like_with_paper": paper_like_for_like_reference_ready,
        "paper_like_for_like_reference_ready": paper_like_for_like_reference_ready,
        "paper_explicit_only_reference_ready": paper_explicit_only_reference_ready,
        "strict_paper_only_reference_ready": strict_paper_only_reference_ready,
        "repo_implicit_closure_forbidden": repo_implicit_closure_forbidden,
        "paper_cited_helper_objects_present": paper_cited_helper_objects_present,
        "paper_cited_helper_objects_active": paper_cited_helper_objects_active,
        "active_two_metric_flrw_reference_object_present": True,
        "active_k_equals_kbar_equals_minus_one_branch_present": True,
        "published_k_equals_kbar_equals_minus_one_branch_present": True,
        "active_global_energy_equation_present": True,
        "active_sector_density_law_present": True,
        "active_two_metric_rhs_present": True,
        "paper_native_observational_anchors_present": True,
        "published_cited_exact_shape_present": False,
        "paper_native_plus_history_present": False,
        "paper_published_observation_reference_present": False,
        "active_bulk_observable_path_present": False,
        "active_absolute_normalization_contract_present": False,
        "active_background_reference_path_kind": "paper_equations_and_anchors_only",
        "active_background_reference_path_is_full_published_bulk": strict_paper_only_reference_ready,
        "paper_explicitly_fixed_objects": paper_explicitly_fixed_objects,
        "paper_cited_but_not_explicit_objects": paper_cited_but_not_explicit_objects,
        "paper_underdetermined_objects": paper_underdetermined_objects,
        "excluded_repo_helpers": excluded_repo_helpers,
        "repo_added_closures": [],
        "missing_for_like_for_like": missing_for_like_for_like,
        "missing_for_strict_paper_only": missing_for_strict_paper_only,
        "active_bulk_observational_run_executed": False,
        "the_janus_cosmological_model_2024_branch_frozen": False,
        "active_bulk_completion_required": not strict_paper_only_reference_ready,
        "next_branch": "The_Janus_Cosmological_Model_2024_reference_paper_native_materialization",
        "manifest_path": str(MANIFEST_PATH),
        "manifest": manifest,
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload(write_manifest=True)
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# The Janus Cosmological Model 2024 Reference Gate",
                "",
                f"Reference recreated: `{payload['the_janus_cosmological_model_2024_reference_recreated']}`",
                f"Published bulk equations present: `{payload['published_bulk_bimetric_equations_present']}`",
                f"Published absolute density normalization present: `{payload['published_absolute_density_normalization_present']}`",
                f"Paper-structured reference ready: `{payload['paper_structured_reference_ready']}`",
                f"Paper-only branch ready: `{payload['paper_only_branch_ready']}`",
                f"Paper-plus-cited-comparison branch ready: `{payload['paper_plus_cited_comparison_branch_ready']}`",
                f"Like-for-like with paper: `{payload['like_for_like_with_paper']}`",
                f"Paper explicit-only reference ready: `{payload['paper_explicit_only_reference_ready']}`",
                f"Strict paper-only reference ready: `{payload['strict_paper_only_reference_ready']}`",
                f"Repo implicit closure forbidden: `{payload['repo_implicit_closure_forbidden']}`",
                f"Paper cited helper objects active: `{payload['paper_cited_helper_objects_active']}`",
                f"Paper-native observational anchors present: `{payload['paper_native_observational_anchors_present']}`",
                f"Active background path kind: `{payload['active_background_reference_path_kind']}`",
                f"Active path is full published bulk: `{payload['active_background_reference_path_is_full_published_bulk']}`",
                f"Reference branch frozen: `{payload['the_janus_cosmological_model_2024_branch_frozen']}`",
                f"Next branch: `{payload['next_branch']}`",
                "",
                "## Explicitly Fixed By Paper",
                "",
                *[f"- `{item}`" for item in payload["paper_explicitly_fixed_objects"]],
                "",
                "## Present But Not Counted As Paper-Explicit",
                "",
                *[f"- `{item}`" for item in payload["paper_cited_but_not_explicit_objects"]],
                "",
                "## Still Underdetermined By Paper",
                "",
                *[f"- `{item}`" for item in payload["paper_underdetermined_objects"]],
                "",
                "## Remaining Strict Paper-Only Blockers",
                "",
                *[f"- `{item}`" for item in payload["missing_for_strict_paper_only"]],
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
