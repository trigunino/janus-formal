from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_mass_shell_b4vol_measure.md")
JSON_PATH = Path("outputs/reports/p0_eft_mass_shell_b4vol_measure.json")


def build_payload() -> dict:
    measures = {
        "liouville": "canonical cotangent lift preserves d^4x d^4p",
        "mass_shell": "dPi_m = sqrt(-g) d^3p / p^0 after delta(H+m^2/2) reduction",
        "lapse_energy": "p^0 normalization depends on the observer/lapse of the receiving sheet",
        "active_source": "T^{mu nu} uses B4vol times transported mass-shell moments",
    }
    b4vol = {
        "meaning": "four-volume determinant bridge for active source density",
        "not_equal_to": "dust 3-volume factor unless comoving dust assumptions are added",
        "candidate": "B4vol = sqrt(-g_other_to_self)/sqrt(-g_self)",
        "closure_condition": "must be derived from the same tetrad soldering used by Phi",
    }
    theorem_status = {
        "mass_shell_measure_defined": True,
        "lapse_energy_factor_identified": True,
        "b4vol_candidate_defined": True,
        "b4vol_derived_from_soldering": False,
        "active_source_measure_closed": False,
        "stress_tensor_moments_closed": False,
        "prediction_ready_unconditional": False,
    }
    obligations = [
        "derive B4vol from the tetrad soldering determinant, not from dust volume",
        "derive receiving-sheet p^0/lapse normalization for dPi_m",
        "then compute T^{mu nu}_other_to_self moments with rho, p, Pi",
    ]
    return {
        "description": "Mass-shell and B4vol active measure target after same-L Liouville bridge.",
        "status": "mass-shell-defined-b4vol-open",
        "measures": measures,
        "b4vol": b4vol,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "Mass-shell measure is structurally defined, but active gravitational source closure "
            "still requires deriving B4vol and the receiving-sheet lapse/energy normalization."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Mass-Shell B4vol Measure",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## Measures",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["measures"].items())
    lines.extend(["", "## B4vol"])
    lines.extend(f"- {key}: {value}" for key, value in payload["b4vol"].items())
    lines.extend(["", "## Status"])
    lines.extend(f"- {key}: {value}" for key, value in payload["theorem_status"].items())
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
