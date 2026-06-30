from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_linear_imatter_l_variation.md")
JSON_PATH = Path("outputs/reports/p0_linear_imatter_l_variation.json")


def build_payload() -> dict:
    variation_rows = [
        {
            "row": "plus_contract",
            "formula": "I = T_plus^{mu nu} L_mu^a T_minus_ab L_nu^b",
            "status": "defined",
        },
        {
            "row": "delta_l",
            "formula": "delta_L I = T_plus^{mu nu} deltaL_mu^a T_minus_ab L_nu^b + T_plus^{mu nu} L_mu^a T_minus_ab deltaL_nu^b",
            "status": "closed-algebraic",
        },
        {
            "row": "symmetric_stress_reduction",
            "formula": "if T_plus,T_minus symmetric: delta_L I = 2 T_plus^{mu nu} deltaL_mu^a T_minus_ab L_nu^b",
            "status": "closed-conditional",
        },
        {
            "row": "e_l_raw",
            "formula": "E_L_mu^a proportional 2 c1 T_plus^{mu nu} T_minus_ab L_nu^b",
            "status": "raw-not-projected",
        },
        {
            "row": "lorentz_projection",
            "formula": "E_L[Omega]=antisym_ab((L^T P)_ab)=0 with Omega_ab=-Omega_ba",
            "status": "closed-algebraic",
        },
    ]
    return {
        "description": "L-variation of the linear I_matter tensor contract.",
        "status": "l-variation-and-lorentz-projection-closed",
        "variation_rows": variation_rows,
        "delta_l_algebra_closed": True,
        "raw_e_l_available": True,
        "lorentz_projected_e_l_closed": True,
        "map_phi_variation_closed": False,
        "split_noether_residuals_evaluated": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The algebraic L variation and Lorentz projection of I_matter are closed. "
            "Phi/pullback and metric variations are still required before Split Noether "
            "residuals can be evaluated."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Linear I_matter L Variation",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Delta L algebra closed: {payload['delta_l_algebra_closed']}",
        f"Raw E_L available: {payload['raw_e_l_available']}",
        f"Lorentz projected E_L closed: {payload['lorentz_projected_e_l_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Variation Rows",
        "",
    ]
    for row in payload["variation_rows"]:
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
