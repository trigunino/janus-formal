from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_isometry_branch_no_go.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_isometry_branch_no_go.json")


def build_payload() -> dict:
    assumptions = [
        "Use the Stueckelberg map Phi to pull minus-sector tensors into the plus chart.",
        "Let L_minus_to_plus be tetrad/Lorentz compatible on the transported frame.",
        "Try to cancel the receiver-connection residual by imposing Phi^* g_plus = g_minus.",
    ]
    consequences = [
        "If Phi is a local isometry, the Levi-Civita connections are transported together.",
        "Then the connection-difference term C_plus-minus^mu_ab u^a u^b vanishes.",
        "The same holds in the mirror direction only if the inverse map is also metric-compatible.",
    ]
    no_go = [
        "Local isometry equates the two metric geometries, not only the dust congruence.",
        "That is stronger than Janus FLRW with distinct sector scale factors a_plus and a_minus.",
        "It risks erasing the two-metric content needed for expansion/lensing-sector differences.",
        "Therefore it cannot be accepted as the generic Janus closure route.",
    ]
    allowed_use = [
        "Use as a diagnostic limit or local tangent-frame consistency check.",
        "Do not use as the production closure unless Janus sources explicitly derive this isometry.",
        "A weaker dust-congruence or connection-gauge condition is still required for the real route.",
    ]
    return {
        "artifact": "p0_stueckelberg_isometry_branch_no_go",
        "status": "bounded-no-go-for-generic-janus",
        "assumptions": assumptions,
        "connection_residual_cancelled_if_isometry": True,
        "generic_janus_admissible": False,
        "source_derived": False,
        "new_axiom_if_used_generically": True,
        "physics_closed": False,
        "prediction_ready": False,
        "consequences": consequences,
        "no_go_reasons": no_go,
        "allowed_use": allowed_use,
        "next_required_derivation": (
            "Derive a weaker map equation that transports the selected dust congruence or "
            "connection component without forcing full metric isometry."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Stueckelberg Isometry Branch No-Go",
        "",
        f"Status: {payload['status']}",
        f"Generic Janus admissible: {payload['generic_janus_admissible']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Assumptions",
    ]
    lines.extend(f"- {item}" for item in payload["assumptions"])
    lines.extend(["", "## Consequences"])
    lines.extend(f"- {item}" for item in payload["consequences"])
    lines.extend(["", "## No-Go Reasons"])
    lines.extend(f"- {item}" for item in payload["no_go_reasons"])
    lines.extend(["", "## Allowed Use"])
    lines.extend(f"- {item}" for item in payload["allowed_use"])
    lines.extend(["", "## Next Required Derivation", payload["next_required_derivation"], ""])
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
