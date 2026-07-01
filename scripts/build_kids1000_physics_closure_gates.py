from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/kids1000_physics_closure_gates.md")
JSON_PATH = Path("outputs/reports/kids1000_physics_closure_gates.json")


GATES = [
    {
        "gate": "primordial_amplitude",
        "closed": False,
        "required": "A_J or P_prim amplitude fixed from Janus IC/CMB before KiDS residuals",
        "forbidden": "choose amplitude from KiDS best-fit scalar",
    },
    {
        "gate": "value_slip_green_kernel",
        "closed": False,
        "required": "convert derivative/kink slip branch into value-level eta_slip_JH(k,a)",
        "forbidden": "set eta_slip by lensing residuals",
    },
    {
        "gate": "nonlinear_small_scale_closure",
        "closed": False,
        "required": "Janus-compatible nonlinear or scale-cut policy beyond linear Weyl shape",
        "forbidden": "import HMCode baryon/nonlinear terms without provenance",
    },
    {
        "gate": "intrinsic_alignment_policy",
        "closed": False,
        "required": "fixed IA prescription or explicit IA-free scale cut before chi2 claim",
        "forbidden": "fit IA nuisance to rescue KiDS",
    },
    {
        "gate": "baryon_feedback_policy",
        "closed": False,
        "required": "fixed baryon feedback policy or excluded scale range",
        "forbidden": "tune feedback against KiDS residuals",
    },
]


def build_payload() -> dict:
    return {
        "description": "Closure gates before a KiDS-1000 Janus-Holst prediction claim.",
        "status": "kids1000-physics-gates-open",
        "gates": GATES,
        "all_closed": all(row["closed"] for row in GATES),
        "prediction_claim_allowed": False,
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# KiDS-1000 Physics Closure Gates",
        "",
        payload["description"],
        "",
        f"Status: `{payload['status']}`",
        f"All closed: `{payload['all_closed']}`",
        f"Prediction claim allowed: `{payload['prediction_claim_allowed']}`",
        "",
        "| gate | closed | required | forbidden |",
        "|---|---|---|---|",
    ]
    for row in payload["gates"]:
        lines.append(f"| {row['gate']} | {row['closed']} | {row['required']} | {row['forbidden']} |")
    lines.append("")
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
