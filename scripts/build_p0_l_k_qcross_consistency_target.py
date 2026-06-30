from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_l_k_qcross_consistency_target.md")
JSON_PATH = Path("outputs/reports/p0_l_k_qcross_consistency_target.json")


def build_payload() -> dict:
    admissible_l_requirements = [
        "L_minus_to_plus^T eta L_minus_to_plus = eta",
        "L_plus_to_minus^T eta L_plus_to_minus = eta",
        "L_plus_to_minus = L_minus_to_plus^{-1} or source-derived mirror map",
        "both maps act on tetrad components, not raw coordinate components",
    ]
    induced_stress_requirements = [
        "K_plus^{AB}=transport_L_minus_to_plus(T_minus^{AB})",
        "K_minus^{AB}=transport_L_plus_to_minus(T_plus^{AB})",
        "K_plus and K_minus must use the same L maps used for optical projection",
        "R_plus^A=0 and R_minus^A=0 must hold before any prediction claim",
    ]
    qcross_requirements = [
        "Q_cross=(eta_AB u_minus_to_plus^A k_plus^B)^2/(eta_AB u_plus^A k_plus^B)^2",
        "u_minus_to_plus^A=L_minus_to_plus^A_B u_minus^B",
        "mirror Q_cross_minus uses L_plus_to_minus and k_minus",
        "the optical Q_cross map cannot differ from the Bianchi K transport map",
    ]
    forbidden_shortcuts = [
        "do not use L_geom=e_plus E_minus as admissible optical transport unless L_geom^T eta L_geom=eta is proved",
        "do not derive K_plus/K_minus from one map and Q_cross from another",
        "do not absorb L/K/Q_cross inconsistencies into scalar Q_det or scalar Q_cross",
        "do not claim lensing or simulation prediction while R_plus or R_minus remains open",
    ]
    open_proof_obligations = [
        "derive L_minus_to_plus from Janus field/source equations",
        "derive L_plus_to_minus or prove it is the inverse/mirror transport",
        "prove Lorentz/tetrad compatibility for both maps",
        "derive K_plus and K_minus from these maps",
        "prove Bianchi residual closure R_plus=0 and R_minus=0",
        "prove the same maps generate the Q_cross optical contractions",
    ]
    return {
        "description": "P0 consistency target linking admissible L transport, induced K stress tensors, and optical Q_cross.",
        "status": "target-open",
        "lorentz_tetrad_compatibility_proved": False,
        "k_transport_induced": False,
        "same_map_for_k_and_qcross": False,
        "residuals_closed": False,
        "prediction_ready": False,
        "admissible_l_requirements": admissible_l_requirements,
        "induced_stress_requirements": induced_stress_requirements,
        "qcross_requirements": qcross_requirements,
        "forbidden_shortcuts": forbidden_shortcuts,
        "open_proof_obligations": open_proof_obligations,
        "verdict": (
            "L, K_plus/K_minus, and Q_cross must be derived as one compatible "
            "transport structure. L_geom remains bookkeeping only unless its "
            "Lorentz condition is proved, and no prediction is allowed before "
            "R_plus=R_minus=0."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 L/K/Q_cross Consistency Target",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Lorentz/tetrad compatibility proved: {payload['lorentz_tetrad_compatibility_proved']}",
        f"K transport induced: {payload['k_transport_induced']}",
        f"Same map for K and Q_cross: {payload['same_map_for_k_and_qcross']}",
        f"Residuals closed: {payload['residuals_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Admissible L Requirements",
        "",
    ]
    lines.extend(f"- `{item}`" for item in payload["admissible_l_requirements"])
    lines.extend(["", "## Induced Stress Requirements", ""])
    lines.extend(f"- `{item}`" for item in payload["induced_stress_requirements"])
    lines.extend(["", "## Q_cross Requirements", ""])
    lines.extend(f"- `{item}`" for item in payload["qcross_requirements"])
    lines.extend(["", "## Forbidden Shortcuts", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_shortcuts"])
    lines.extend(["", "## Open Proof Obligations", ""])
    lines.extend(f"- {item}" for item in payload["open_proof_obligations"])
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
