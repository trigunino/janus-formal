from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_flrw_irreducible_torsion_pullback_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_flrw_irreducible_torsion_pullback_gate.json")
COMPONENTS_PATH = Path("outputs/active_z2_sigma/flrw_irreducible_torsion_components.json")


def _load_components(path: Path) -> dict:
    if not path.exists():
        return {}
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("FLRW irreducible torsion active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("FLRW irreducible torsion source must be active_derived")
    for key in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_reuse_used",
        "archived_z4_background_reuse_used",
        "phenomenological_holst_bao_scan_used",
        "observational_H0_fit_used",
        "observational_curvature_fit_used",
    ]:
        if payload.get(key, False) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")
    return payload


def build_payload(
    *,
    sigma_torsion_pullback_ready: bool = False,
    irreducible_components_payload: dict | None = None,
    components_path: Path = COMPONENTS_PATH,
) -> dict:
    components = irreducible_components_payload or _load_components(components_path)
    declared = {
        "Riemann_Cartan_irreducible_torsion_split_imported": True,
        "FLRW_symmetry_reduction_declared": True,
        "trace_axial_tensor_components_declared": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "Sigma_torsion_pullback_ready": bool(sigma_torsion_pullback_ready),
        "trace_vector_component_ready": bool(components.get("trace_vector_component_ready", False)),
        "axial_vector_component_ready": bool(components.get("axial_vector_component_ready", False)),
        "tensor_torsion_component_ready": bool(components.get("tensor_torsion_component_ready", False)),
    }
    ready = all(declared.values()) and all(closure.values())
    if not closure["Sigma_torsion_pullback_ready"]:
        primary_blocker = "Sigma_torsion_pullback"
    elif not closure["trace_vector_component_ready"]:
        primary_blocker = "trace_vector_torsion_component"
    elif not closure["axial_vector_component_ready"]:
        primary_blocker = "axial_vector_torsion_component"
    elif not closure["tensor_torsion_component_ready"]:
        primary_blocker = "tensor_torsion_component"
    else:
        primary_blocker = "none"
    return {
        "status": "janus-z2-sigma-flrw-irreducible-torsion-pullback-gate",
        "active_core": "Z2_tunnel_Sigma",
        "declared": declared,
        "closure": closure,
        "formulas": {
            "irreducible_split": "T_{abc} -> T_a(trace) + A_a(axial) + q_{abc}(tensor)",
            "flrw_reduction": "FLRW symmetry fixes which pulled-back torsion components survive on Sigma",
        },
        "FLRW_irreducible_torsion_pullback_ready": ready,
        "gate_passed": ready,
        "primary_blocker": primary_blocker,
        "current_frontier": [
            f"{key} = false"
            for key, value in closure.items()
            if not value
        ],
        "next_required": []
        if ready
        else [
            "derive_Sigma_torsion_pullback",
            "reduce_trace_vector_axial_vector_tensor_torsion_components",
            "prove_FLRW_symmetry_allowed_components_on_Sigma",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma FLRW Irreducible Torsion Pullback Gate",
        "",
        f"Ready: `{payload['FLRW_irreducible_torsion_pullback_ready']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        "## Current Frontier",
    ]
    lines.extend(f"- `{item}`" for item in payload["current_frontier"])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
