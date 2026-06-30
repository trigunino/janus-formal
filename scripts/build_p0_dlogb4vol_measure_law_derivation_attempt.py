from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_dlogb4vol_measure_law_derivation_attempt.md")
JSON_PATH = Path("outputs/reports/p0_dlogb4vol_measure_law_derivation_attempt.json")


def build_payload() -> dict:
    measure_conventions = [
        {
            "name": "B_4vol",
            "definition": "B_4vol_receiver_from_source=sqrt(-g_source)/sqrt(-g_receiver)",
            "contains": "lapse ratio and spatial slice determinant ratio",
            "must_not_be_conflated_with": "V3_dust or rho_to",
        },
        {
            "name": "V3_dust",
            "definition": "dust slice-volume density factor selected by the continuity convention",
            "contains": "spatial volume only unless an explicit lapse reinsertion is proven",
            "must_not_be_conflated_with": "B_4vol",
        },
        {
            "name": "rho_to",
            "definition": "transported source dust density as seen in the receiver frame",
            "contains": "matter density, not determinant bookkeeping",
            "must_not_be_conflated_with": "Q_det or Q_cross",
        },
    ]
    product_rule_targets = [
        {
            "receiver": "plus",
            "source": "minus",
            "target": "D_plus_nu(B_4vol_plus_from_minus rho_minus_to_plus u_minus_to_plus^nu)=0",
            "expanded": (
                "B_4vol_plus_from_minus D_plus_nu(rho_minus_to_plus u_minus_to_plus^nu) "
                "+ B_4vol_plus_from_minus rho_minus_to_plus "
                "u_minus_to_plus^nu D_plus_nu log(B_4vol_plus_from_minus)=0"
            ),
            "residual_substitution": (
                "D_plus_nu(rho_minus_to_plus u_minus_to_plus^nu) "
                "-> -rho_minus_to_plus u_minus_to_plus^nu "
                "D_plus_nu log(B_4vol_plus_from_minus)"
            ),
            "closed": False,
        },
        {
            "receiver": "minus",
            "source": "plus",
            "target": "D_minus_nu(B_4vol_minus_from_plus rho_plus_to_minus u_plus_to_minus^nu)=0",
            "expanded": (
                "B_4vol_minus_from_plus D_minus_nu(rho_plus_to_minus u_plus_to_minus^nu) "
                "+ B_4vol_minus_from_plus rho_plus_to_minus "
                "u_plus_to_minus^nu D_minus_nu log(B_4vol_minus_from_plus)=0"
            ),
            "residual_substitution": (
                "D_minus_nu(rho_plus_to_minus u_plus_to_minus^nu) "
                "-> -rho_plus_to_minus u_plus_to_minus^nu "
                "D_minus_nu log(B_4vol_minus_from_plus)"
            ),
            "closed": False,
        },
    ]
    required_identities = [
        "Janus source identity for D_receiver log N_source - D_receiver log N_receiver",
        "Janus source identity for D_receiver log gamma_source - D_receiver log gamma_receiver",
        "slice-to-4D lapse reinsertion identity relating V3_dust to B_4vol",
        "transported density law for D_receiver(rho_to u_to^nu)",
        "transported velocity/tetrad law fixing D_receiver u_to^nu terms before contraction",
        "mirror consistency for plus_from_minus and minus_from_plus determinant derivatives",
    ]
    forbidden_operations = [
        "absorb D log B_4vol into Q_det",
        "absorb D log B_4vol into Q_cross",
        "multiply by Q_det after B_4vol has already been included",
        "count both V3_dust and B_4vol as the same determinant measure",
        "replace the lapse-bearing B_4vol law with a pure 3-volume dust law",
    ]
    return {
        "description": (
            "Bounded P0 derivation attempt for a D log B_4vol measure law. "
            "It tracks the four-dimensional determinant measure separately from "
            "the three-volume dust density and writes the algebraic product-rule targets."
        ),
        "status": "derivation-attempt-open",
        "b4vol_separated_from_v3_dust": True,
        "rho_to_separated_from_measure": True,
        "product_rule_targets_written": True,
        "residual_substitution_written": True,
        "qdet_qcross_scalar_absorption_forbidden": True,
        "double_counting_forbidden": True,
        "source_identities_supplied": False,
        "physics_closed": False,
        "prediction_ready": False,
        "measure_conventions": measure_conventions,
        "product_rule_targets": product_rule_targets,
        "required_identities": required_identities,
        "forbidden_operations": forbidden_operations,
        "verdict": (
            "This artifact fixes the algebraic target and substitution ledger only. "
            "It is not prediction-ready and does not close the physics until the "
            "listed Janus source, slice, and lapse identities are derived."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 DlogB4vol Measure-Law Derivation Attempt",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"B_4vol separated from V3_dust: {payload['b4vol_separated_from_v3_dust']}",
        f"rho_to separated from measure: {payload['rho_to_separated_from_measure']}",
        f"Product-rule targets written: {payload['product_rule_targets_written']}",
        f"Residual substitution written: {payload['residual_substitution_written']}",
        f"Q_det/Q_cross scalar absorption forbidden: {payload['qdet_qcross_scalar_absorption_forbidden']}",
        f"Double counting forbidden: {payload['double_counting_forbidden']}",
        f"Source identities supplied: {payload['source_identities_supplied']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Measure Conventions",
        "",
    ]
    for row in payload["measure_conventions"]:
        lines.append(f"- {row['name']}:")
        lines.append(f"  - definition: `{row['definition']}`")
        lines.append(f"  - contains: {row['contains']}")
        lines.append(f"  - must not be conflated with: {row['must_not_be_conflated_with']}")
    lines.extend(["", "## Product-Rule Targets", ""])
    for row in payload["product_rule_targets"]:
        lines.append(f"- {row['receiver']} receives {row['source']}:")
        lines.append(f"  - target: `{row['target']}`")
        lines.append(f"  - expanded: `{row['expanded']}`")
        lines.append(f"  - residual substitution: `{row['residual_substitution']}`")
        lines.append(f"  - closed: {row['closed']}")
    lines.extend(["", "## Required Janus Identities", ""])
    lines.extend(f"- {item}" for item in payload["required_identities"])
    lines.extend(["", "## Forbidden Operations", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_operations"])
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
