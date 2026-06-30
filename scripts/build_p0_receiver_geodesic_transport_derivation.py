from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_receiver_geodesic_transport_derivation.md")
JSON_PATH = Path("outputs/reports/p0_receiver_geodesic_transport_derivation.json")


def build_payload() -> dict:
    own_geodesics = [
        "negative matter: u_-^b D_minus_b u_-^a=0",
        "positive matter: u_+^b D_plus_b u_+^a=0",
    ]
    transported_geodesics = [
        {
            "direction": "negative_to_positive",
            "definition": "u_-to+^A=L_-+^A_B u_-^B",
            "receiver_geodesic": "u_-to+^B D_plus_B u_-to+^A=0",
            "expanded_l_condition": (
                "u_-to+^B F_-+^A_{C B}u_-^C + "
                "u_-to+^B L_-+^A_C D_plus_B u_-^C = 0"
            ),
            "connection_form": (
                "u_-to+^B D_minus_B u_-to+^A + "
                "C^A_{BC}u_-to+^C u_-to+^B=0"
            ),
        },
        {
            "direction": "positive_to_negative",
            "definition": "u_+to-^A=L_+-^A_B u_+^B",
            "receiver_geodesic": "u_+to-^B D_minus_B u_+to-^A=0",
            "expanded_l_condition": (
                "u_+to-^B F_+-^A_{C B}u_+^C + "
                "u_+to-^B L_+-^A_C D_minus_B u_+^C = 0"
            ),
            "connection_form": (
                "u_+to-^B D_plus_B u_+to-^A - "
                "C^A_{BC}u_+to-^C u_+to-^B=0"
            ),
        },
    ]
    derivation_status = [
        "own-sector Janus geodesics are source-anchored by the two metric families",
        "receiver-geodesic transported flows are stronger conditions than own-sector geodesics",
        "F must supply the missing acceleration conversion between source and receiver connections",
        "Fermi-Walker sets rotation after receiver-geodesic flow is given; it does not derive that flow",
    ]
    acceptance_requirements = [
        "derive the expanded L condition from Janus action, symmetry, or field/source equations",
        "show both directions use mirror-compatible L maps",
        "show the same transported u enters K_plus/K_minus and Q_cross",
        "combine with transported continuity and density-measure terms to close residuals",
    ]
    forbidden_shortcuts = [
        "do not replace receiver-geodesic with own-sector geodesic",
        "do not set the expanded F term to zero without source reason",
        "do not infer global transport from a local Lorentz boost",
        "do not hide the receiver acceleration in fitted Q_cross",
    ]
    return {
        "description": "Derivation target for receiver-geodesic transported flows in the primary P0 branch.",
        "status": "receiver-geodesic-transport-open",
        "own_geodesics_source_anchored": True,
        "receiver_geodesics_derived": False,
        "expanded_l_conditions_written": True,
        "fermi_walker_derives_receiver_flow": False,
        "physics_closed": False,
        "prediction_ready": False,
        "own_geodesics": own_geodesics,
        "transported_geodesics": transported_geodesics,
        "derivation_status": derivation_status,
        "acceptance_requirements": acceptance_requirements,
        "forbidden_shortcuts": forbidden_shortcuts,
        "verdict": (
            "The two Janus geodesic families anchor own-sector motion, but Bianchi "
            "closure requires the transported flow to be geodesic for the receiver "
            "connection. This is an explicit condition on F, not yet a source-derived law."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Receiver-Geodesic Transport Derivation",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Own geodesics source-anchored: {payload['own_geodesics_source_anchored']}",
        f"Receiver geodesics derived: {payload['receiver_geodesics_derived']}",
        f"Expanded L conditions written: {payload['expanded_l_conditions_written']}",
        f"Fermi-Walker derives receiver flow: {payload['fermi_walker_derives_receiver_flow']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Own Geodesics",
        "",
    ]
    lines.extend(f"- `{item}`" for item in payload["own_geodesics"])
    lines.extend(["", "## Transported Geodesics", ""])
    for row in payload["transported_geodesics"]:
        lines.append(f"- {row['direction']}:")
        lines.append(f"  - definition: `{row['definition']}`")
        lines.append(f"  - receiver geodesic: `{row['receiver_geodesic']}`")
        lines.append(f"  - expanded L condition: `{row['expanded_l_condition']}`")
        lines.append(f"  - connection form: `{row['connection_form']}`")
    lines.extend(["", "## Derivation Status", ""])
    lines.extend(f"- {item}" for item in payload["derivation_status"])
    lines.extend(["", "## Acceptance Requirements", ""])
    lines.extend(f"- {item}" for item in payload["acceptance_requirements"])
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
