from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_density_measure_closure_condition.md")
JSON_PATH = Path("outputs/reports/p0_density_measure_closure_condition.json")


def build_payload() -> dict:
    determinant_definitions = [
        "B_plus=sqrt(-g_minus)/sqrt(-g_plus)",
        "B_minus=sqrt(-g_plus)/sqrt(-g_minus)",
        "FLRW: B_plus=(N_minus a_minus^3 sqrt(gamma_minus))/(N_plus a_plus^3 sqrt(gamma_plus))",
        "dust 3-volume ratio omits lapse and must not be silently substituted for B_plus",
    ]
    product_rule_terms = [
        "D_plus_B(B_plus K_plus^{AB}) = B_plus D_plus_B K_plus^{AB} + K_plus^{AB} D_plus_B log(B_plus)",
        "D_minus_B(B_minus K_minus^{AB}) = B_minus D_minus_B K_minus^{AB} + K_minus^{AB} D_minus_B log(B_minus)",
    ]
    dust_closure_requirements = [
        {
            "sector": "plus",
            "required_flux": "D_minus_B(rho_minus u_-to+^B)",
            "extra_measure_term": "rho_minus u_-to+^A u_-to+^B D_plus_B log(B_plus)",
            "closure_condition": (
                "transported continuity must include or cancel the B_plus gradient term "
                "under the selected density measure"
            ),
        },
        {
            "sector": "minus",
            "required_flux": "D_plus_B(rho_plus u_+to-^B)",
            "extra_measure_term": "rho_plus u_+to-^A u_+to-^B D_minus_B log(B_minus)",
            "closure_condition": (
                "transported continuity must include or cancel the B_minus gradient term "
                "under the selected density measure"
            ),
        },
    ]
    admissible_conventions = [
        {
            "name": "field_equation_4volume",
            "uses_lapse": True,
            "status": "candidate source convention",
            "risk": "requires lapse/slice fixed before numerical use",
        },
        {
            "name": "dust_flux_3volume",
            "uses_lapse": False,
            "status": "candidate continuity convention",
            "risk": "must be reconciled with 4-volume determinant in field equations",
        },
        {
            "name": "effective_density_absorbs_B",
            "uses_lapse": "depends on B",
            "status": "diagnostic bookkeeping",
            "risk": "can hide double-counting if mixed with Q_det again",
        },
    ]
    forbidden_shortcuts = [
        "do not drop D log B terms",
        "do not set B_plus=1 except in an explicitly proven approximation",
        "do not use raw (a_minus/a_plus)^3 or ^4 as lensing amplitude",
        "do not merge Q_det with Q_cross",
    ]
    return {
        "description": "P0 density-measure closure condition for B_plus/B_minus in transported Bianchi residuals.",
        "status": "density-measure-closure-open",
        "product_rule_terms_written": True,
        "d_log_b_terms_required": True,
        "source_convention_fixed": False,
        "b_gradients_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "determinant_definitions": determinant_definitions,
        "product_rule_terms": product_rule_terms,
        "dust_closure_requirements": dust_closure_requirements,
        "admissible_conventions": admissible_conventions,
        "forbidden_shortcuts": forbidden_shortcuts,
        "verdict": (
            "B_plus/B_minus are not passive labels: their gradients enter the Bianchi "
            "residuals. Density-measure closure requires a source-derived convention "
            "that either includes or cancels D log B terms."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Density-Measure Closure Condition",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Product-rule terms written: {payload['product_rule_terms_written']}",
        f"D log B terms required: {payload['d_log_b_terms_required']}",
        f"Source convention fixed: {payload['source_convention_fixed']}",
        f"B gradients closed: {payload['b_gradients_closed']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Determinant Definitions",
        "",
    ]
    lines.extend(f"- `{item}`" for item in payload["determinant_definitions"])
    lines.extend(["", "## Product-Rule Terms", ""])
    lines.extend(f"- `{item}`" for item in payload["product_rule_terms"])
    lines.extend(["", "## Dust Closure Requirements", ""])
    for row in payload["dust_closure_requirements"]:
        lines.append(f"- {row['sector']}:")
        lines.append(f"  - required flux: `{row['required_flux']}`")
        lines.append(f"  - extra measure term: `{row['extra_measure_term']}`")
        lines.append(f"  - closure condition: {row['closure_condition']}")
    lines.extend(["", "## Admissible Conventions", ""])
    for row in payload["admissible_conventions"]:
        lines.append(
            f"- {row['name']}: uses_lapse={row['uses_lapse']}; status={row['status']}; risk={row['risk']}"
        )
    lines.extend(["", "## Forbidden Shortcuts", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_shortcuts"])
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
