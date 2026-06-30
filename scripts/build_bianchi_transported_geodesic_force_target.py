from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/bianchi_transported_geodesic_force_target.md")
JSON_PATH = Path("outputs/reports/bianchi_transported_geodesic_force_target.json")


def build_payload() -> dict:
    connection_identities = [
        "C^mu_{nu a}=Gamma_plus^mu_{nu a}-Gamma_minus^mu_{nu a}",
        "D_plus_u v^mu = D_minus_u v^mu + C^mu_{nu a} v^a u^nu",
        "D_minus_u v^mu = D_plus_u v^mu - C^mu_{nu a} v^a u^nu",
    ]
    transported_geodesic_targets = [
        {
            "sector": "negative_to_positive",
            "target": "u_{-to+}^nu D_plus_nu u_{-to+}^mu=0",
            "equivalent_force": "u_{-to+}^nu D_minus_nu u_{-to+}^mu + C^mu_{nu a} u_{-to+}^a u_{-to+}^nu=0",
            "closes": "positive residual K_plus force bracket",
        },
        {
            "sector": "positive_to_negative",
            "target": "u_{+to-}^nu D_minus_nu u_{+to-}^mu=0",
            "equivalent_force": "u_{+to-}^nu D_plus_nu u_{+to-}^mu - C^mu_{nu a} u_{+to-}^a u_{+to-}^nu=0",
            "closes": "negative residual K_minus force bracket",
        },
    ]
    source_requirements = [
        "derive why transported negative flow is D_plus-geodesic",
        "derive why transported positive flow is D_minus-geodesic",
        "derive L maps that preserve normalization and time orientation",
        "combine with transported continuity to close full dust K residuals",
    ]
    forbidden_shortcuts = [
        "same-sector geodesic does not imply transported receiver-sector geodesic",
        "local Lorentz boost does not imply D_plus geodesic globally",
        "do not drop C terms instead of proving receiver-connection geodesics",
    ]
    return {
        "description": "Receiver-connection geodesic target for cancelling Bianchi connection-force terms.",
        "status": "force-equation-target",
        "force_cancellation_equivalent_to_receiver_geodesic": True,
        "receiver_geodesics_source_derived": False,
        "physics_closed": False,
        "prediction_ready": False,
        "connection_identities": connection_identities,
        "transported_geodesic_targets": transported_geodesic_targets,
        "source_requirements": source_requirements,
        "forbidden_shortcuts": forbidden_shortcuts,
        "verdict": (
            "The connection-force equation can be rephrased as receiver-connection "
            "geodesic motion of the transported flow. This is a sharper P0 target, "
            "not yet a Janus-derived proof."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Bianchi Transported Geodesic Force Target",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Force cancellation equivalent to receiver geodesic: {payload['force_cancellation_equivalent_to_receiver_geodesic']}",
        f"Receiver geodesics source-derived: {payload['receiver_geodesics_source_derived']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Connection Identities",
        "",
    ]
    lines.extend(f"- `{item}`" for item in payload["connection_identities"])
    lines.extend(["", "## Transported Geodesic Targets", ""])
    lines.extend(["| sector | target | equivalent force | closes |", "|---|---|---|---|"])
    for row in payload["transported_geodesic_targets"]:
        lines.append(
            f"| {row['sector']} | `{row['target']}` | `{row['equivalent_force']}` | {row['closes']} |"
        )
    lines.extend(["", "## Source Requirements", ""])
    lines.extend(f"- {item}" for item in payload["source_requirements"])
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
