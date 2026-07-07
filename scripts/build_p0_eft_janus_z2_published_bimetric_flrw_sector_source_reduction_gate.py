from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_bianchi_flrw_dust_transport_branch import build_payload as dust
from scripts.build_bianchi_flrw_lapse_volume_audit import build_payload as lapse_volume
from scripts.build_bianchi_flrw_perfect_fluid_transport_branch import (
    build_payload as perfect_fluid,
)
from scripts.build_p0_eft_janus_z2_global_bimetric_source_scale_audit_gate import (
    build_payload as global_source_scale,
)
from scripts.build_p0_eft_janus_z2_global_bimetric_stress_energy_mass_reducer_gate import (
    build_payload as global_mass_state,
)
from scripts.build_p0_eft_janus_z2_global_bimetric_state_to_flrw_sector_normalization_gate import (
    build_payload as sector_normalization,
)
from scripts.build_p0_eft_janus_z2_published_bimetric_sector_ratio_gate import (
    build_payload as sector_ratio,
)
from scripts.build_p0_eft_janus_z2_published_bimetric_symbolic_sector_sources import (
    build_payload as symbolic_sources,
)


JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_published_bimetric_flrw_sector_source_reduction_gate.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_published_bimetric_flrw_sector_source_reduction_gate.md")


def build_payload() -> dict[str, Any]:
    dust_payload = dust()
    lapse_payload = lapse_volume()
    pf_payload = perfect_fluid()
    global_scale_payload = global_source_scale()
    global_mass_payload = global_mass_state()
    sector_norm_payload = sector_normalization()
    sector_ratio_payload = sector_ratio()
    symbolic_sources_payload = symbolic_sources()
    rho_p_shape_ready = bool(
        dust_payload["branch_closed"] and lapse_payload["determinant_formula_closed"]
    )
    return {
        "status": "janus-z2-published-bimetric-flrw-sector-source-reduction-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source": "published_bimetric_FLRW_scalar_sector",
        "shape_level": {
            "dust_scalar_transport_closed": dust_payload["branch_closed"],
            "determinant_formula_closed": lapse_payload["determinant_formula_closed"],
            "rho_p_shape_ready": rho_p_shape_ready,
            "plus_shape": "rho_+(a)=rho_+0*a_+^-3 for dust; cross weight uses declared determinant/transport layer",
            "minus_shape": "rho_-(a)=rho_-0*a_-^-3 for dust; cross weight uses declared determinant/transport layer",
        },
        "conditional_pressure_level": {
            "perfect_fluid_transport_conditional": True,
            "branch_closed": pf_payload["branch_closed"],
            "blocked_by": pf_payload["blockers"],
        },
        "normalization_level": {
            "plus_normalization_derived": False,
            "minus_normalization_derived": False,
            "relative_sector_ratio_ready": sector_ratio_payload[
                "relative_sector_ratio_ready"
            ],
            "rho_minus0_over_rho_plus0": sector_ratio_payload["ratio_payload"][
                "rho_minus0_over_rho_plus0"
            ],
            "absolute_density_scale_ready": sector_ratio_payload[
                "absolute_density_scale_ready"
            ],
            "symbolic_sector_sources_ready": symbolic_sources_payload[
                "symbolic_sector_sources_ready"
            ],
            "global_bimetric_equations_available": global_scale_payload[
                "global_bimetric_equations_available"
            ],
            "absolute_mass_scale_found": global_scale_payload["absolute_mass_scale_found"],
            "global_stress_energy_mass_available": global_mass_payload[
                "global_stress_energy_mass_available"
            ],
            "sector_normalizations_ready": sector_norm_payload[
                "sector_normalizations_ready"
            ],
            "allowed_sources": [
                "action-derived state/Noether charge",
                "published Janus global solution mass-density normalization",
                "declared superselection state with explicit provenance",
            ],
            "forbidden_sources": [
                "observational fit",
                "reuse LCDM omega_b/omega_cdm",
                "reuse N_gap as density without projection map",
            ],
        },
        "rho_p_normalized_ready": sector_norm_payload["sector_normalizations_ready"],
        "sector_source_ready_for_sigma_pullback": sector_norm_payload[
            "sector_normalizations_ready"
        ],
        "primary_blocker": (
            "none"
            if sector_norm_payload["sector_normalizations_ready"]
            else "plus_minus_density_normalizations"
        ),
        "upstream_global_scale_audit": {
            "status": global_scale_payload["status"],
            "missing_inputs": global_scale_payload["missing_inputs"],
        },
        "upstream_global_mass_state": {
            "status": global_mass_payload["status"],
            "input_exists": global_mass_payload["input_exists"],
            "global_stress_energy_mass_available": global_mass_payload[
                "global_stress_energy_mass_available"
            ],
            "next_required": global_mass_payload["next_required"],
        },
        "upstream_sector_normalization": {
            "status": sector_norm_payload["status"],
            "ready": sector_norm_payload["sector_normalizations_ready"],
            "primary_blocker": sector_norm_payload["primary_blocker"],
            "next_required": sector_norm_payload["next_required"],
        },
        "upstream_sector_ratio": {
            "status": sector_ratio_payload["status"],
            "relative_ready": sector_ratio_payload["relative_sector_ratio_ready"],
            "absolute_scale_ready": sector_ratio_payload["absolute_density_scale_ready"],
            "rho_minus0_over_rho_plus0": sector_ratio_payload["ratio_payload"][
                "rho_minus0_over_rho_plus0"
            ],
        },
        "upstream_symbolic_sector_sources": {
            "status": symbolic_sources_payload["status"],
            "ready": symbolic_sources_payload["symbolic_sector_sources_ready"],
            "missing_input": symbolic_sources_payload["source_manifest"][
                "missing_input"
            ],
        },
        "next_required": [
            "derive absolute rho_+0 from a Janus bimetric state or Noether charge",
            "then set rho_-0 from the published relative sector ratio",
            "or select a published exact Janus FLRW solution with its own normalization",
            "then write normalized sector stress T_±(a) before Sigma projection",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Published Bimetric FLRW Sector Source Reduction Gate",
        "",
        f"rho/p shape ready: `{payload['shape_level']['rho_p_shape_ready']}`",
        f"relative sector ratio ready: `{payload['normalization_level']['relative_sector_ratio_ready']}`",
        f"rho/p normalized ready: `{payload['rho_p_normalized_ready']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
