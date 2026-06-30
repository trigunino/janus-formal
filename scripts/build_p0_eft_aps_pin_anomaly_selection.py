from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_aps_pin_anomaly_selection.md")
JSON_PATH = Path("outputs/reports/p0_eft_aps_pin_anomaly_selection.json")


def build_payload() -> dict:
    aps_data = {
        "manifold": "Janus orbifold with fixed hypersurface Sigma",
        "operator": "Dirac-Cartan operator with PT/Pin boundary condition",
        "index_object": "eta invariant / mod-2 Pin anomaly",
        "selection_rule": "healthy Pin structure has vanishing global parity anomaly",
    }
    pin_table = [
        {
            "pin": "Pin+",
            "pt_square": "+1",
            "eta_anomaly": "nonzero_mod2",
            "accepted": False,
            "reason": "global parity anomaly remains",
        },
        {
            "pin": "Pin-",
            "pt_square": "-1",
            "eta_anomaly": "zero_mod2",
            "accepted": True,
            "reason": "global parity anomaly cancels conditionally",
        },
    ]
    obligations = [
        "define the Janus Dirac-Cartan operator and its domain",
        "specify Pin+ and Pin- boundary conditions on Sigma",
        "compute or formalize the eta invariant difference",
        "prove Pin+ has nonzero anomaly and Pin- has zero anomaly",
        "then promote q_A = sign(Sigma)/sqrt(6) from conditional to selected",
    ]
    theorem_status = {
        "aps_selection_map_written": True,
        "dirac_operator_domain_defined": False,
        "eta_invariant_computed": False,
        "pin_minus_selected_conditionally": True,
        "pin_minus_selected_proved": False,
        "prediction_ready": False,
    }
    return {
        "description": "APS/eta-invariant obligation map for selecting Pin- in the Janus EFT route.",
        "status": "aps-anomaly-selection-map-open",
        "theorem_status": theorem_status,
        "aps_data": aps_data,
        "pin_table": pin_table,
        "obligations": obligations,
        "verdict": (
            "This is the exact remaining topological proof target. Pin- is selected only "
            "conditionally until the eta/mod-2 anomaly calculation is supplied."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT APS Pin Anomaly Selection",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
    ]
    lines.extend(f"{key}: {value}" for key, value in payload["theorem_status"].items())
    lines.extend(["", "## Pin Table"])
    for row in payload["pin_table"]:
        lines.append(
            f"- {row['pin']}: PT^2={row['pt_square']}, "
            f"eta={row['eta_anomaly']}, accepted={row['accepted']}"
        )
    lines.extend(["", "## Obligations"])
    lines.extend(f"- {item}" for item in payload["obligations"])
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
