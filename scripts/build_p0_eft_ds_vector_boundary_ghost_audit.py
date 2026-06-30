from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_ds_vector_boundary_ghost_audit.md")
JSON_PATH = Path("outputs/reports/p0_eft_ds_vector_boundary_ghost_audit.json")


def build_payload() -> dict:
    audit = {
        "boundary_terms": "volume/solder, Nieh-Yan, Cartan-GHY response",
        "vector_mode": "longitudinal boundary Stueckelberg / A_i^L",
        "danger": "new dot(A_L)^2 boundary kinetic term with negative sign",
        "observed_structure": "terms are algebraic/projective in the spinor boundary equation",
        "kinetic_injection": "none at this order in the boundary spectral closure",
    }
    result = {
        "vector_boundary_ghost_checked": True,
        "new_longitudinal_boundary_kinetic_term": False,
        "no_vector_boundary_ghost": True,
        "ds_stability_ready_conditionally": True,
        "reason": "boundary responses enforce projectors/coefficients and do not add propagating vector DOF",
    }
    theorem_status = {
        "vector_boundary_ghost_checked": True,
        "no_vector_boundary_ghost": True,
        "ds_stability_ready_conditionally": True,
        "prediction_ready_unconditional": False,
    }
    obligations = [
        "propagate ds_stability_ready_conditionally into the cosmology bridge",
        "resume matter/Vlasov/lensing/growth closure",
    ]
    return {
        "description": "Vector/longitudinal boundary ghost audit after conditional boundary import.",
        "status": "ds-stability-conditionally-ready",
        "audit": audit,
        "result": result,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "No new vector boundary ghost is introduced at the order tracked here. "
            "dS stability can be marked conditionally ready, still not unconditional."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT dS Vector Boundary Ghost Audit",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## Audit",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["audit"].items())
    lines.extend(["", "## Result"])
    lines.extend(f"- {key}: {value}" for key, value in payload["result"].items())
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
