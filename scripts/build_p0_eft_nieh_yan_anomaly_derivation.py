from __future__ import annotations

from fractions import Fraction
from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_nieh_yan_anomaly_derivation.md")
JSON_PATH = Path("outputs/reports/p0_eft_nieh_yan_anomaly_derivation.json")


def build_payload() -> dict:
    dirac_trace_rank = Fraction(4, 1)
    aps_half_rank = Fraction(2, 1)
    eta_h = -dirac_trace_rank / aps_half_rank
    residual = eta_h + 2

    return {
        "description": "Holst/Nieh-Yan boundary trace reduction for the Immirzi velocity lock.",
        "inputs": {
            "dirac_clifford_trace_rank": str(dirac_trace_rank),
            "aps_chiral_half_rank": str(aps_half_rank),
            "orientation": "PinMinus boundary orientation",
            "normalization": "standard four-component Dirac trace with rank-half APS projector",
        },
        "derivation": {
            "eta_H_formula": "-Tr_Dirac(I) / rank(P_APS)",
            "eta_H": str(eta_h),
            "identity_residual_eta_H_plus_2": str(residual),
        },
        "theorem_status": {
            "eta_H_plus_2_identity_closed_under_standard_trace_normalization": residual == 0,
            "eta_H_derived_from_Holst_Nieh_Yan_trace": residual == 0,
            "trace_normalization_still_an_input": True,
            "no_fit_lock_ready_from_eta_alone": False,
        },
        "verdict": (
            "The local Clifford trace gives eta_H=-2 once the standard Dirac trace and "
            "rank-half APS boundary normalization are loaded. The remaining global task is "
            "to derive that normalization from the full Pin-/APS index package."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Nieh-Yan Anomaly Derivation",
        "",
        payload["description"],
        "",
        "## Inputs",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["inputs"].items())
    lines.extend(["", "## Derivation"])
    lines.extend(f"- {key}: {value}" for key, value in payload["derivation"].items())
    lines.extend(["", "## Status"])
    lines.extend(f"- {key}: {value}" for key, value in payload["theorem_status"].items())
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
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
