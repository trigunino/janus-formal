from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_dlogb_4volume_obstruction.md")
JSON_PATH = Path("outputs/reports/p0_dlogb_4volume_obstruction.json")


def build_payload() -> dict:
    dlogb_identities = [
        {
            "identity": "D_plus_alpha log B_4vol_plus_from_minus",
            "definition": "B_4vol_plus_from_minus = sqrt(-g_minus) / sqrt(-g_plus)",
            "expanded": (
                "D_plus_alpha log N_minus - D_plus_alpha log N_plus "
                "+ 1/2 D_plus_alpha log gamma_minus "
                "- 1/2 D_plus_alpha log gamma_plus"
            ),
            "needed_for": "product-rule terms in R_plus",
            "status": "source-identity-missing",
        },
        {
            "identity": "D_minus_alpha log B_4vol_minus_from_plus",
            "definition": "B_4vol_minus_from_plus = sqrt(-g_plus) / sqrt(-g_minus)",
            "expanded": (
                "D_minus_alpha log N_plus - D_minus_alpha log N_minus "
                "+ 1/2 D_minus_alpha log gamma_plus "
                "- 1/2 D_minus_alpha log gamma_minus"
            ),
            "needed_for": "product-rule terms in R_minus",
            "status": "source-identity-missing",
        },
    ]
    residual_product_rules = [
        {
            "residual": "R_plus",
            "term": (
                "D_plus_alpha(B_4vol_plus_from_minus K_minus_to_plus) "
                "= B_4vol_plus_from_minus D_plus_alpha K_minus_to_plus "
                "+ K_minus_to_plus D_plus_alpha B_4vol_plus_from_minus"
            ),
            "requires": "D_plus_alpha log B_4vol_plus_from_minus",
            "closed": False,
        },
        {
            "residual": "R_minus",
            "term": (
                "D_minus_alpha(B_4vol_minus_from_plus K_plus_to_minus) "
                "= B_4vol_minus_from_plus D_minus_alpha K_plus_to_minus "
                "+ K_plus_to_minus D_minus_alpha B_4vol_minus_from_plus"
            ),
            "requires": "D_minus_alpha log B_4vol_minus_from_plus",
            "closed": False,
        },
    ]
    missing_source_identities = [
        "source-derived relation between cross-derivatives of lapse N_plus/N_minus",
        "source-derived relation between cross-derivatives of slice determinants gamma_plus/gamma_minus",
        "source-derived split proving when gamma ratio reduces to FLRW a-ratio terms",
        "source-derived transport law linking B_4vol product-rule terms to K residual cancellation",
        "mirror identity showing the plus and minus B_4vol derivatives cancel consistently",
    ]
    forbidden_replacements = [
        "replace B_4vol with V3_dust",
        "replace D log B_4vol with raw a-ratio derivative",
        "absorb the obstruction into scalar Q_cross",
        "absorb the obstruction into scalar Q_det",
    ]
    return {
        "description": (
            "Bounded P0 artifact for the D log B_4vol blocker: B_4vol is a "
            "four-volume measure ratio and must not be conflated with V3_dust."
        ),
        "status": "obstruction-open",
        "b4vol_separated_from_v3_dust": True,
        "lapse_terms_included": True,
        "slice_terms_included": True,
        "product_rule_terms_written": True,
        "prediction_ready": False,
        "physics_closed": False,
        "dlogb_identities": dlogb_identities,
        "residual_product_rules": residual_product_rules,
        "missing_source_identities": missing_source_identities,
        "forbidden_replacements": forbidden_replacements,
        "verdict": (
            "This is a blocker artifact, not a closure claim. Prediction and "
            "physics remain false until the listed source-derived identities "
            "are supplied."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 DlogB 4-Volume Obstruction",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"B_4vol separated from V3_dust: {payload['b4vol_separated_from_v3_dust']}",
        f"Lapse terms included: {payload['lapse_terms_included']}",
        f"Slice terms included: {payload['slice_terms_included']}",
        f"Product-rule terms written: {payload['product_rule_terms_written']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## D log B_4vol Identities",
        "",
    ]
    for row in payload["dlogb_identities"]:
        lines.append(f"- `{row['identity']}`")
        lines.append(f"  - definition: `{row['definition']}`")
        lines.append(f"  - expanded: `{row['expanded']}`")
        lines.append(f"  - needed for: {row['needed_for']}")
        lines.append(f"  - status: {row['status']}")
    lines.extend(["", "## Residual Product Rules", ""])
    for row in payload["residual_product_rules"]:
        lines.append(f"- `{row['residual']}`")
        lines.append(f"  - term: `{row['term']}`")
        lines.append(f"  - requires: `{row['requires']}`")
        lines.append(f"  - closed: {row['closed']}")
    lines.extend(["", "## Missing Source-Derived Identities", ""])
    lines.extend(f"- {item}" for item in payload["missing_source_identities"])
    lines.extend(["", "## Forbidden Replacements", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_replacements"])
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
