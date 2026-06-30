from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_janus_equations_to_dlogb4vol_closure_attempt.md")
JSON_PATH = Path("outputs/reports/p0_janus_equations_to_dlogb4vol_closure_attempt.json")


def build_payload() -> dict:
    janus_ingredients = [
        {
            "name": "determinant source layer",
            "source": "M15 Eqs. 4a-4b",
            "formula": "G_plus = chi(T_plus + B_4vol_plus_from_minus T_minus_to_plus)",
            "role": "anchors B_4vol in the plus active cross-source slot",
            "closed": True,
        },
        {
            "name": "mirror determinant source layer",
            "source": "M15 Eqs. 4a-4b",
            "formula": "G_minus = -chi(B_4vol_minus_from_plus T_plus_to_minus + T_minus)",
            "role": "anchors the reciprocal determinant layer in the minus equation",
            "closed": True,
        },
        {
            "name": "Bianchi residual target",
            "source": "Janus coupled equations plus Bianchi identity D_receiver G_receiver = 0",
            "formula": "D_receiver(T_receiver + B_4vol_receiver_from_source T_source_to_receiver) = 0",
            "role": "forces product-rule D log B_4vol terms instead of scalar absorption",
            "closed": False,
        },
    ]
    measure_ledger = [
        {
            "symbol": "B_4vol",
            "definition": "sqrt(-g_source)/sqrt(-g_receiver)",
            "contains": "lapse and spatial-slice determinant factors",
            "separate_from": ["V3_dust", "rho_to", "Q_det", "Q_cross"],
        },
        {
            "symbol": "V3_dust",
            "definition": "dust continuity three-volume factor",
            "contains": "slice volume only unless a lapse identity is derived",
            "separate_from": ["B_4vol", "rho_to", "Q_det"],
        },
        {
            "symbol": "rho_to",
            "definition": "source density transported into the receiver description",
            "contains": "matter density, not determinant bookkeeping",
            "separate_from": ["B_4vol", "V3_dust", "Q_det", "Q_cross"],
        },
        {
            "symbol": "Q_det",
            "definition": "lensing/source normalization label for determinant-density convention",
            "contains": "bookkeeping label only in this artifact",
            "separate_from": ["B_4vol", "V3_dust", "rho_to", "Q_cross"],
        },
    ]
    product_rule_identities = [
        {
            "sector": "plus",
            "identity": (
                "D_plus_nu(B_4vol_plus_from_minus rho_minus_to_plus u_minus_to_plus^nu) = "
                "B_4vol_plus_from_minus D_plus_nu(rho_minus_to_plus u_minus_to_plus^nu) + "
                "B_4vol_plus_from_minus rho_minus_to_plus u_minus_to_plus^nu "
                "D_plus_nu log B_4vol_plus_from_minus"
            ),
            "closure_condition": (
                "D_plus_nu(rho_minus_to_plus u_minus_to_plus^nu) = "
                "-rho_minus_to_plus u_minus_to_plus^nu D_plus_nu log B_4vol_plus_from_minus"
            ),
            "closed": False,
        },
        {
            "sector": "minus",
            "identity": (
                "D_minus_nu(B_4vol_minus_from_plus rho_plus_to_minus u_plus_to_minus^nu) = "
                "B_4vol_minus_from_plus D_minus_nu(rho_plus_to_minus u_plus_to_minus^nu) + "
                "B_4vol_minus_from_plus rho_plus_to_minus u_plus_to_minus^nu "
                "D_minus_nu log B_4vol_minus_from_plus"
            ),
            "closure_condition": (
                "D_minus_nu(rho_plus_to_minus u_plus_to_minus^nu) = "
                "-rho_plus_to_minus u_plus_to_minus^nu D_minus_nu log B_4vol_minus_from_plus"
            ),
            "closed": False,
        },
    ]
    missing_identities = [
        "source identity for D_receiver log sqrt(-g_source) from Janus determinant/source equations",
        "source identity for D_receiver log sqrt(-g_receiver) in the same receiver derivative",
        "slice identity connecting V3_dust to the spatial determinant part of B_4vol",
        "lapse identity proving the lapse ratio may be inserted or removed from the dust law",
        "transport law for D_receiver(rho_to u_to^nu) before replacing it by a D log B_4vol term",
        "velocity/tetrad identity for D_receiver u_to^nu and connection-difference terms",
        "mirror reciprocity identity for plus_from_minus and minus_from_plus determinant derivatives",
    ]
    forbidden_operations = [
        "absorb D log B_4vol into Q_det",
        "absorb D log B_4vol into Q_cross",
        "count B_4vol and V3_dust as the same determinant factor",
        "multiply rho_to by Q_det after B_4vol has already weighted the source",
        "claim closure from determinant equations without the source/slice/lapse identities",
    ]
    return {
        "description": "Bounded P0 attempt from Janus determinant/source equations to D log B_4vol closure.",
        "status": "closure-attempt-open",
        "janus_ingredients": janus_ingredients,
        "measure_ledger": measure_ledger,
        "product_rule_identities": product_rule_identities,
        "missing_identities": missing_identities,
        "forbidden_operations": forbidden_operations,
        "b4vol_v3_dust_rho_to_qdet_distinct": True,
        "janus_source_determinant_bianchi_ingredients_listed": True,
        "product_rule_identities_derived": True,
        "source_slice_lapse_identities_missing": True,
        "qdet_qcross_absorption_forbidden": True,
        "double_counting_forbidden": True,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The Janus determinant/source equations select the B_4vol cross-source slot and "
            "Bianchi supplies the product-rule target, but D log B_4vol closure is still open "
            "until the listed source, slice, lapse, density, and transport identities are derived."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Equations to DlogB4vol Closure Attempt",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"B_4vol/V3_dust/rho_to/Q_det distinct: {payload['b4vol_v3_dust_rho_to_qdet_distinct']}",
        f"Product-rule identities derived: {payload['product_rule_identities_derived']}",
        f"Source/slice/lapse identities missing: {payload['source_slice_lapse_identities_missing']}",
        f"Q_det/Q_cross absorption forbidden: {payload['qdet_qcross_absorption_forbidden']}",
        f"Double counting forbidden: {payload['double_counting_forbidden']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Janus Ingredients",
        "",
    ]
    for row in payload["janus_ingredients"]:
        lines.append(f"- {row['name']} ({row['source']}): `{row['formula']}`")
        lines.append(f"  - role: {row['role']}")
        lines.append(f"  - closed: {row['closed']}")
    lines.extend(["", "## Measure Ledger", ""])
    for row in payload["measure_ledger"]:
        lines.append(f"- {row['symbol']}: `{row['definition']}`")
        lines.append(f"  - contains: {row['contains']}")
        lines.append(f"  - separate from: {row['separate_from']}")
    lines.extend(["", "## Product-Rule Identities", ""])
    for row in payload["product_rule_identities"]:
        lines.append(f"- {row['sector']}: `{row['identity']}`")
        lines.append(f"  - closure condition: `{row['closure_condition']}`")
        lines.append(f"  - closed: {row['closed']}")
    lines.extend(["", "## Missing Identities", ""])
    lines.extend(f"- {item}" for item in payload["missing_identities"])
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
