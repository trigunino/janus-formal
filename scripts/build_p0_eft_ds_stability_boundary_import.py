from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_ds_stability_boundary_import.md")
JSON_PATH = Path("outputs/reports/p0_eft_ds_stability_boundary_import.json")


def build_payload() -> dict:
    imported_boundary = {
        "boundary_projector": "P_chiral from conditional boundary EL closure",
        "eta_sector": "eta_mod2=0 conditionally via APS/Pin-",
        "volume_response": "lambda=-4*q_T",
        "cartan_response": "beta*Delta_chi=-sigma*(1+tau)/2",
        "nieh_yan_response": "kappa=2*q_A*Delta_chi",
    }
    ds_stability = {
        "tensor": "unchanged by scalar boundary projector except through response bookkeeping",
        "vector": "requires no new longitudinal ghost from boundary response",
        "scalar": "boundary projector removes the previously dangerous spinor/spectral channel",
        "zero_modes": "absent conditionally on compact Riemannian APS boundary with H^2>0",
    }
    theorem_status = {
        "boundary_conditions_imported": True,
        "tensor_sector_consistent_conditionally": True,
        "scalar_spinor_boundary_channel_consistent_conditionally": True,
        "vector_boundary_ghost_checked": False,
        "ds_stability_ready_conditionally": False,
        "prediction_ready_unconditional": False,
    }
    obligations = [
        "audit vector/longitudinal boundary response for new ghost terms",
        "recompute scalar dS kinetic matrix with boundary response assumptions explicitly listed",
        "then mark dS stability conditionally ready if no new boundary kinetic term appears",
    ]
    return {
        "description": "Import conditional boundary closure into dS scalar/tensor stability bookkeeping.",
        "status": "ds-boundary-import-partial-vector-audit-open",
        "imported_boundary": imported_boundary,
        "ds_stability": ds_stability,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "The boundary closure is compatible with tensor/scalar bookkeeping conditionally. "
            "The remaining dS-specific check is whether vector/longitudinal boundary response "
            "reintroduces a ghost."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT dS Stability Boundary Import",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## Imported Boundary",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["imported_boundary"].items())
    lines.extend(["", "## dS Stability"])
    lines.extend(f"- {key}: {value}" for key, value in payload["ds_stability"].items())
    lines.extend(["", "## Status"])
    lines.extend(f"- {key}: {value}" for key, value in payload["theorem_status"].items())
    lines.extend(["", "## Obligations"])
    lines.extend(f"- {item}" for item in payload["obligations"])
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
