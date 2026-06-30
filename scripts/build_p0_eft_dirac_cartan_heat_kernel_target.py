from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_dirac_cartan_heat_kernel_target.md")
JSON_PATH = Path("outputs/reports/p0_eft_dirac_cartan_heat_kernel_target.json")


def build_payload() -> dict:
    laplace_type_data = {
        "operator": "D_C^2 = -(nabla_C)^2 + E_C",
        "connection": "nabla_C = Levi-Civita spin connection + Cartan/torsion/radion connection",
        "endomorphism": "E_C contains R/4 plus torsion/radion derivative terms",
        "curvature": "Omega_C contains spin curvature plus torsion/radion field strength",
    }
    a4_sources = [
        {
            "term": "tr(E_C^2)",
            "can_generate": "torsion/radion derivative square and mixed curvature scalar contacts",
            "double_dual_relevance": "partial",
        },
        {
            "term": "tr(R E_C)",
            "can_generate": "R * (nabla chi)^2 type operators",
            "double_dual_relevance": "partial",
        },
        {
            "term": "tr(Omega_C_mn Omega_C^mn)",
            "can_generate": "curvature-torsion contractions; candidate source for Ricci/Einstein-tensor derivative coupling",
            "double_dual_relevance": "main",
        },
        {
            "term": "boundary a4 coefficients",
            "can_generate": "K, D_i K, and orbifold boundary projection terms",
            "double_dual_relevance": "required for k4 boundary completion",
        },
    ]
    checks = [
        {
            "id": "DC1",
            "statement": "Dirac-Cartan heat-kernel can generate curvature-radion operators",
            "status": "plausible_by_structure",
        },
        {
            "id": "DC2",
            "statement": "the generated tower is automatically the Horndeski/double-dual combination",
            "status": "not_proved",
        },
        {
            "id": "DC3",
            "statement": "non-Horndeski terms are removed by orbifold/no-ghost projection",
            "status": "open",
        },
        {
            "id": "DC4",
            "statement": "boundary a4 terms generate the exact k4 completion coefficient",
            "status": "open",
        },
    ]
    theorem_status = {
        "dirac_cartan_target_written": True,
        "laplace_type_reduction_done": False,
        "a4_coefficients_computed": False,
        "double_dual_identified_in_a4": False,
        "exact_contact_coefficient_matched": False,
        "prediction_ready": False,
    }
    return {
        "description": "Target specification for the first Dirac-Cartan heat-kernel calculation.",
        "status": "dirac-cartan-heat-kernel-target-written-not-computed",
        "theorem_status": theorem_status,
        "laplace_type_data": laplace_type_data,
        "a4_sources": a4_sources,
        "checks": checks,
        "next_steps": [
            "choose explicit torsion/radion connection A_mu(chi)",
            "square the Dirac-Cartan operator into Laplace form",
            "extract E_C and Omega_C",
            "compute a4 bulk and boundary structures",
            "test whether projection leaves exactly the double-dual/Horndeski operator",
        ],
        "verdict": (
            "No new physics input is needed to write the target. Actual computation still needs "
            "the explicit torsion/radion connection and boundary conditions."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Dirac-Cartan Heat-Kernel Target",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
    ]
    lines.extend(f"{key}: {value}" for key, value in payload["theorem_status"].items())
    lines.extend(["", "## A4 Sources"])
    for row in payload["a4_sources"]:
        lines.append(f"- {row['term']}: {row['can_generate']} ({row['double_dual_relevance']})")
    lines.extend(["", "## Checks"])
    for row in payload["checks"]:
        lines.append(f"- {row['id']}: {row['statement']} -> {row['status']}")
    lines.extend(["", "## Next Steps"])
    lines.extend(f"- {item}" for item in payload["next_steps"])
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
