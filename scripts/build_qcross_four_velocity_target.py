from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/qcross_four_velocity_target.md")
JSON_PATH = Path("outputs/reports/qcross_four_velocity_target.json")


def build_payload() -> dict:
    sections = {
        "equal_projection": {
            "status": "current convention",
            "claim": "Q_cross = 1 under an explicit equal-projection assumption.",
            "admissible_now": True,
            "blocks_final_claim": True,
            "rule": "Use only when the equal-projection branch is named in the formula.",
        },
        "local_velocity_bridge": {
            "status": "local diagnostic bridge",
            "claim": (
                "Q_cross = gamma_-^2 (1 - beta_vec.n_photon)^2 in a local positive "
                "orthonormal frame."
            ),
            "admissible_now": True,
            "blocks_final_claim": True,
            "rule": (
                "Requires declared velocity calibration and a local photon direction; "
                "it is not a global tensor closure."
            ),
        },
        "missing_global_four_velocity_closure": {
            "status": "missing",
            "claim": (
                "A covariant projection of negative-sector four-velocity/stress via "
                "L_minus_to_plus along positive-sector null rays has not been derived."
            ),
            "admissible_now": False,
            "blocks_final_claim": True,
            "rule": "Keep Q_cross explicit until the L_minus_to_plus tetrad/covector map is derived.",
        },
        "pm_usage_conditions": {
            "status": "conditional PM use",
            "claim": (
                "PM outputs may feed Q_cross diagnostics only after source-derived beta "
                "fields and physical velocity/time calibration are declared."
            ),
            "admissible_now": True,
            "blocks_final_claim": True,
            "rule": (
                "Do not treat PM Q_cross diagnostics as survey predictions or final "
                "physical evidence."
            ),
        },
    }
    return {
        "description": "Target scaffold for separating Q_cross four-velocity projection layers.",
        "physics_closed": False,
        "sections": sections,
        "verdict": (
            "Equal projection and the local velocity bridge are usable named scaffolds. "
            "The global L_minus_to_plus tetrad/covector closure is still missing, "
            "so the physics is not closed."
        ),
    }


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")

    lines = [
        "# Q_cross Four-Velocity Projection Target",
        "",
        payload["description"],
        "",
        f"Physics closed: {payload['physics_closed']}",
        "",
        "| section | status | claim | admissible now | blocks final claim | rule |",
        "|---|---|---|---|---|---|",
    ]
    for name, section in payload["sections"].items():
        lines.append(
            f"| `{name}` | {section['status']} | {section['claim']} | "
            f"{section['admissible_now']} | {section['blocks_final_claim']} | "
            f"{section['rule']} |"
        )
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
