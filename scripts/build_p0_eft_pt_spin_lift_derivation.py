from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_pt_spin_lift_derivation.md")
JSON_PATH = Path("outputs/reports/p0_eft_pt_spin_lift_derivation.json")


def build_payload() -> dict:
    derivation_steps = [
        {
            "id": "SL1",
            "statement": "PT reflection acts on the Janus orthonormal frame bundle",
            "status": "assumed_from_orbifold_geometry",
        },
        {
            "id": "SL2",
            "statement": "the PT frame action admits a lift to Spin(3,1) or Pin(3,1)",
            "status": "requires_pin_structure_choice",
        },
        {
            "id": "SL3",
            "statement": "the lifted loop around the fixed surface has chirality generator gamma5",
            "status": "conditional_on_pin_lift",
        },
        {
            "id": "SL4",
            "statement": "canonical radion normalization maps holonomy magnitude to 1/sqrt(6)",
            "status": "normalization_condition_not_derived_here",
        },
        {
            "id": "SL5",
            "statement": "sheet pairing cancels parity-odd residues",
            "status": "follows_if_orbifold_even_pairing_is_imposed",
        },
    ]
    obstruction = {
        "missing_choice": "Pin+/Pin- lift and spin structure around the orbifold fixed surface",
        "why_it_matters": "different lifts can change the sign or remove the axial holonomy",
        "cannot_be_inferred_from_metric_only": True,
    }
    consequence_if_closed = {
        "q_T": "1",
        "q_A": "sign(Sigma)/sqrt(6)",
        "branch": "paired axial trace torsion",
        "next": "Dirac-Cartan heat-kernel a4 with fixed q_A/q_T",
    }
    theorem_status = {
        "pt_frame_action_identified": True,
        "spin_or_pin_lift_chosen": False,
        "chirality_holonomy_derived": False,
        "q_A_fixed": False,
        "prediction_ready": False,
    }
    return {
        "description": "Attempted derivation of Janus PT spin lift and axial holonomy coefficient.",
        "status": "blocked-on-pin-structure-choice",
        "theorem_status": theorem_status,
        "derivation_steps": derivation_steps,
        "obstruction": obstruction,
        "consequence_if_closed": consequence_if_closed,
        "verdict": (
            "Metric/orbifold geometry alone does not determine the spin lift. To derive q_A, "
            "Janus must specify a Pin/Spin structure or equivalent PT action on bulk spinors."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT PT Spin Lift Derivation",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
    ]
    lines.extend(f"{key}: {value}" for key, value in payload["theorem_status"].items())
    lines.extend(["", "## Steps"])
    for row in payload["derivation_steps"]:
        lines.append(f"- {row['id']}: {row['statement']} -> {row['status']}")
    lines.extend(["", "## Obstruction"])
    for key, value in payload["obstruction"].items():
        lines.append(f"- {key}: {value}")
    lines.extend(["", "## Consequence If Closed"])
    for key, value in payload["consequence_if_closed"].items():
        lines.append(f"- {key}: {value}")
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
