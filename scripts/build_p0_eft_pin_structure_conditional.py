from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_pin_structure_conditional.md")
JSON_PATH = Path("outputs/reports/p0_eft_pin_structure_conditional.json")


def build_payload() -> dict:
    pin_options = [
        {
            "structure": "Pin+",
            "pt_square": "+1",
            "global_parity_anomaly": "nonzero",
            "healthy": False,
            "q_A": "not accepted",
        },
        {
            "structure": "Pin-",
            "pt_square": "-1",
            "global_parity_anomaly": "zero",
            "healthy": True,
            "q_A": "sign(Sigma)/sqrt(6)",
        },
    ]
    axiom = {
        "id": "A_PinPTSpinStructure",
        "statement": "Janus orbifold selects the anomaly-free Pin- lift whose PT loop acts chirally on bulk spinors",
        "role": "fixes q_A = sign(Sigma)/sqrt(6)",
        "source_derived_from_metric": False,
        "selected_by_global_anomaly_cancellation": True,
        "aps_index_calculation_done": False,
        "observational_fit": False,
    }
    implications = [
        "PT frame reflection lifts to the spinor bundle",
        "bulk spinors acquire chiral holonomy around the fixed surface",
        "odd axial terms cancel by sheet pairing",
        "paired axial trace torsion branch becomes geometrically fixed",
        "Dirac-Cartan heat-kernel target has fixed q_A/q_T",
    ]
    theorem_status = {
        "pin_structure_axiom_written": True,
        "pin_minus_selected_by_anomaly_filter": True,
        "aps_index_calculation_done": False,
        "q_A_fixed_conditionally": True,
        "metric_only_derivation": False,
        "observational_fit": False,
        "prediction_ready": False,
    }
    return {
        "description": "Conditional Pin/PT spin-structure axiom for fixing the axial torsion coefficient.",
        "status": "pin-structure-conditional-not-metric-derived",
        "theorem_status": theorem_status,
        "pin_options": pin_options,
        "axiom": axiom,
        "implications": implications,
        "verdict": (
            "Pin- is the clean topological selection if global parity-anomaly cancellation is accepted. "
            "This is not a fit, but it remains conditional until the APS/index anomaly calculation is done."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Pin Structure Conditional",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
    ]
    lines.extend(f"{key}: {value}" for key, value in payload["theorem_status"].items())
    lines.extend(["", "## Pin Options"])
    for row in payload["pin_options"]:
        lines.append(
            f"- {row['structure']}: PT^2={row['pt_square']}, "
            f"anomaly={row['global_parity_anomaly']}, healthy={row['healthy']}, q_A={row['q_A']}"
        )
    lines.extend(["", "## Axiom"])
    for key, value in payload["axiom"].items():
        lines.append(f"- {key}: {value}")
    lines.extend(["", "## Implications"])
    lines.extend(f"- {item}" for item in payload["implications"])
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
