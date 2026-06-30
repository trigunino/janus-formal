from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_linear_imatter_lorentz_projected_el.md")
JSON_PATH = Path("outputs/reports/p0_linear_imatter_lorentz_projected_el.json")


def build_payload() -> dict:
    projection_rows = [
        {
            "row": "raw_momentum",
            "formula": "P_mu^a = 2 c1 T_plus^{mu nu} T_minus_ab L_nu^b",
            "status": "from-delta-L-algebra",
        },
        {
            "row": "lorentz_generator_variation",
            "formula": "deltaL_mu^a = L_mu^b Omega_b^a, Omega_ab=-Omega_ba",
            "status": "admissible-variation",
        },
        {
            "row": "projected_el",
            "formula": "E_L[Omega] = antisym_ab((L^T P)_ab)=0",
            "status": "closed-algebraic",
        },
        {
            "row": "symmetric_part",
            "formula": "sym_ab((L^T P)_ab) is not an admissible Lorentz equation",
            "status": "rejected-as-constraint-leak",
        },
    ]
    return {
        "description": "Lorentz-projected E_L equation for the linear I_matter candidate.",
        "status": "lorentz-projected-el-closed-algebraic",
        "projection_rows": projection_rows,
        "raw_e_l_available": True,
        "lorentz_projected_e_l_closed": True,
        "projected_equation": "antisym_ab((L^T P)_ab)=0",
        "fixes_l_uniquely": False,
        "requires_phi_variation": True,
        "requires_metric_variation": True,
        "split_noether_residuals_evaluated": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The admissible Lorentz projection of the raw E_L is now algebraically closed. "
            "It supplies only the antisymmetric generator equation and does not by itself "
            "fix L uniquely or evaluate R_plus/R_minus."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Linear I_matter Lorentz-Projected E_L",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Raw E_L available: {payload['raw_e_l_available']}",
        f"Lorentz projected E_L closed: {payload['lorentz_projected_e_l_closed']}",
        f"Projected equation: `{payload['projected_equation']}`",
        f"Fixes L uniquely: {payload['fixes_l_uniquely']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Projection Rows",
        "",
    ]
    for row in payload["projection_rows"]:
        lines.append(f"- {row['row']}: `{row['formula']}` ({row['status']})")
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
