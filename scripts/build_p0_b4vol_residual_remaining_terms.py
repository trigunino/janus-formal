from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_b4vol_residual_remaining_terms.md")
JSON_PATH = Path("outputs/reports/p0_b4vol_residual_remaining_terms.json")


def build_payload() -> dict:
    product_rule_residuals = [
        {
            "sector": "R_plus",
            "expanded": "D_plus(B_4vol_plus_from_minus K_minus_to_plus)=B_4vol D_plus K_minus_to_plus + K_minus_to_plus D_plus B_4vol",
            "open_terms": ["D_plus log B_4vol", "D L_minus_to_plus", "connection-difference force"],
            "closed": False,
        },
        {
            "sector": "R_minus",
            "expanded": "D_minus(B_4vol_minus_from_plus K_plus_to_minus)=B_4vol D_minus K_plus_to_minus + K_plus_to_minus D_minus B_4vol",
            "open_terms": ["D_minus log B_4vol", "D L_plus_to_minus", "mirror connection-difference force"],
            "closed": False,
        },
    ]
    dlogb_required_pieces = [
        "D log N_other/N_self",
        "3 D log a_other/a_self or spatial determinant equivalent",
        "1/2 D log gamma_other/gamma_self",
        "no replacement by dust 3-volume without lapse proof",
    ]
    return {
        "description": "Remaining product-rule terms after conditional B_4vol source-measure selection.",
        "status": "b4vol-product-rule-open",
        "product_rule_residuals": product_rule_residuals,
        "dlogb_required_pieces": dlogb_required_pieces,
        "b4vol_product_rule_written": True,
        "dlogb_identity_source_derived": False,
        "dl_identity_source_derived": False,
        "connection_force_closed": False,
        "r_plus_closed": False,
        "r_minus_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "B_4vol selection leaves explicit product-rule terms. Closure requires "
            "source-derived DlogB, D L, and connection-force cancellation identities."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 B4vol Residual Remaining Terms",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"B4vol product rule written: {payload['b4vol_product_rule_written']}",
        f"DlogB identity source-derived: {payload['dlogb_identity_source_derived']}",
        f"R plus closed: {payload['r_plus_closed']}",
        f"R minus closed: {payload['r_minus_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Product Rule Residuals",
        "",
    ]
    for row in payload["product_rule_residuals"]:
        lines.append(f"- {row['sector']}: `{row['expanded']}`")
        lines.append(f"  - open terms: {row['open_terms']}")
        lines.append(f"  - closed: {row['closed']}")
    lines.extend(["", "## DlogB Required Pieces", ""])
    lines.extend(f"- {item}" for item in payload["dlogb_required_pieces"])
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
