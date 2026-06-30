from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_pulled_dust_el_projection_derivation.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_pulled_dust_el_projection_derivation.json")


def build_payload() -> dict:
    derivation_chain = [
        {
            "step": "pulled_dust_action",
            "identity": "S_dust[Phi,L]=int B rho u u contracted with pulled metric/tetrad data",
            "status": "target-form",
        },
        {
            "step": "density_volume_variation",
            "identity": "delta(B rho) terms cancel by Jacobian/volume/DlogB identities",
            "status": "blocked-by-measure-law",
        },
        {
            "step": "velocity_tetrad_variation",
            "identity": "delta_L u terms reduce to transported acceleration plus connection difference",
            "status": "blocked-by-DL-law",
        },
        {
            "step": "transverse_projection",
            "identity": "h E_{Phi,L} = rho h C(u,u)",
            "status": "target-not-derived",
        },
        {
            "step": "mirror_inverse",
            "identity": "minus identity follows from inverse Phi/L, not an independent equation",
            "status": "open",
        },
    ]
    acceptance_checks = [
        "start from pulled dust action, not a generic force target",
        "expand delta_Phi and delta_L terms explicitly",
        "isolate transverse projector h",
        "show density/volume pieces cancel or remain named blockers",
        "show remaining force is exactly rho h Cuu",
        "no transverse multiplier and no weak-congruence axiom",
    ]
    return {
        "description": "Derivation target for the projected Stueckelberg EL dust source hE=rho hCuu.",
        "status": "pulled-dust-el-projection-open",
        "derivation_chain": derivation_chain,
        "acceptance_checks": acceptance_checks,
        "projected_el_source_derived": False,
        "measure_terms_closed": False,
        "dl_terms_closed": False,
        "mirror_inverse_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "This is the concrete derivation needed next. It can close the dust Cuu "
            "sub-blocker only if measure, D L and mirror terms are derived, not imposed."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Stueckelberg Pulled Dust EL Projection Derivation",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Projected EL source derived: {payload['projected_el_source_derived']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Derivation Chain",
        "",
    ]
    for row in payload["derivation_chain"]:
        lines.append(f"- {row['step']}: `{row['identity']}` ({row['status']})")
    lines.extend(["", "## Acceptance Checks", ""])
    lines.extend(f"- {item}" for item in payload["acceptance_checks"])
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
