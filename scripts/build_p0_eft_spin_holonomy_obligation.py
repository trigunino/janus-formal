from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_spin_holonomy_obligation.md")
JSON_PATH = Path("outputs/reports/p0_eft_spin_holonomy_obligation.json")


def build_payload() -> dict:
    obligations = [
        {
            "id": "SH1",
            "statement": "Janus PT reflection lifts from frame bundle to spin bundle",
            "proved": False,
        },
        {
            "id": "SH2",
            "statement": "loop around orbifold defect induces chiral holonomy",
            "proved": False,
        },
        {
            "id": "SH3",
            "statement": "canonical radion normalization fixes holonomy magnitude to 1/sqrt(6)",
            "proved": False,
        },
        {
            "id": "SH4",
            "statement": "sheet pairing cancels parity-odd axial residues",
            "proved": False,
        },
    ]
    consequence_if_proved = {
        "q_T": "1",
        "q_A": "sign(Sigma)/sqrt(6)",
        "branch": "R_paired_axial_trace",
        "next_heat_kernel_test": "Dirac-Cartan a4 with paired axial trace torsion",
    }
    theorem_status = {
        "spin_holonomy_obligation_written": True,
        "pt_spin_lift_proved": False,
        "q_A_geometrically_fixed": False,
        "parity_odd_residue_cancelled": False,
        "prediction_ready": False,
    }
    return {
        "description": "Obligations needed to turn q_A into a Janus-geometric spin-holonomy coefficient.",
        "status": "spin-holonomy-obligation-open",
        "theorem_status": theorem_status,
        "obligations": obligations,
        "consequence_if_proved": consequence_if_proved,
        "verdict": (
            "Trace-only fails structurally. The next non-free, non-fit route is to prove this "
            "spin-holonomy package; otherwise q_A remains an EFT parameter."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Spin-Holonomy Obligation",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
    ]
    lines.extend(f"{key}: {value}" for key, value in payload["theorem_status"].items())
    lines.extend(["", "## Obligations"])
    for row in payload["obligations"]:
        lines.append(f"- {row['id']}: {row['statement']} (proved={row['proved']})")
    lines.extend(["", "## Consequence If Proved"])
    for key, value in payload["consequence_if_proved"].items():
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
