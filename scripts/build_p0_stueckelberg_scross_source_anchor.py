from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_scross_source_anchor.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_scross_source_anchor.json")


def build_payload() -> dict:
    anchors = [
        {
            "source": "M15",
            "anchor": "Eq. 5 and after Eq. 6",
            "content": "same signs attract; opposite signs repel in the double Newtonian approximation",
        },
        {
            "source": "M30",
            "anchor": "Eqs. 105a-105b and after Eq. 106",
            "content": "mixed stationary field equations and Newtonian interaction laws",
        },
        {
            "source": "docs/source_traceability.md",
            "anchor": "Janus interaction laws",
            "content": "weak-field sign matrix verified-source and implemented",
        },
    ]
    sign_matrix = [
        {
            "ray_metric": "g_plus",
            "source": "positive",
            "s_source": "+1",
            "effect": "attractive focusing branch",
        },
        {
            "ray_metric": "g_plus",
            "source": "negative",
            "s_source": "-1",
            "effect": "repulsive / negative-lensing diagnostic branch",
        },
        {
            "ray_metric": "g_minus",
            "source": "positive",
            "s_source": "-1",
            "effect": "mirror repulsive branch",
        },
        {
            "ray_metric": "g_minus",
            "source": "negative",
            "s_source": "+1",
            "effect": "mirror same-sector attractive branch",
        },
    ]
    decision = {
        "s_cross_weak_field_value": "-1",
        "source_anchored": True,
        "scope": "weak-field / reduced Sachs diagnostic",
        "full_tensor_sign_closed": False,
        "prediction_ready": False,
        "reason": (
            "M15/M30 fix the cross-sector weak-field interaction sign: opposite signs "
            "repel. Therefore the reduced positive-photon negative-source Sachs "
            "diagnostic uses s_cross=-1. The exact tensor sign remains tied to the "
            "unclosed K/transport/projection derivation."
        ),
    }
    return {
        "artifact": "p0_stueckelberg_scross_source_anchor",
        "status": "scross-weak-field-fixed-tensor-open",
        "fit_used": False,
        "free_parameters": [],
        "physics_closed": False,
        "prediction_ready": False,
        "anchors": anchors,
        "sign_matrix": sign_matrix,
        "decision": decision,
    }


def render_markdown(payload: dict) -> str:
    decision = payload["decision"]
    lines = [
        "# P0 Stueckelberg s_cross Source Anchor",
        "",
        f"Status: {payload['status']}",
        f"Fit used: {payload['fit_used']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Anchors",
    ]
    for row in payload["anchors"]:
        lines.append(f"- {row['source']} {row['anchor']}: {row['content']}")
    lines.extend(["", "## Sign Matrix"])
    for row in payload["sign_matrix"]:
        lines.append(f"- {row['ray_metric']} / {row['source']}: s={row['s_source']}; {row['effect']}")
    lines.extend(
        [
            "",
            "## Decision",
            f"s_cross weak-field value: {decision['s_cross_weak_field_value']}",
            f"Source anchored: {decision['source_anchored']}",
            f"Scope: {decision['scope']}",
            f"Full tensor sign closed: {decision['full_tensor_sign_closed']}",
            f"Prediction ready: {decision['prediction_ready']}",
            f"Reason: {decision['reason']}",
            "",
        ]
    )
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    payload = build_payload()
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    return payload


if __name__ == "__main__":
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")
