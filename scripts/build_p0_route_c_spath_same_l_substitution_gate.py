from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_l_k_qcross_consistency_target import build_payload as build_l_k_qcross
from scripts.build_p0_route_c_spath_lorentz_tetrad_variation_gate import (
    build_payload as build_spath_lorentz,
)
from scripts.build_p0_same_l_bridge_induces_m_k_qcross_gate import (
    build_payload as build_same_l_bridge,
)


REPORT_PATH = Path("outputs/reports/p0_route_c_spath_same_l_substitution_gate.md")
JSON_PATH = Path("outputs/reports/p0_route_c_spath_same_l_substitution_gate.json")


def build_payload() -> dict:
    spath_lorentz = build_spath_lorentz()
    same_l_bridge = build_same_l_bridge()
    l_k_qcross = build_l_k_qcross()
    substitution_rows = [
        {
            "slot": "spath_el_law",
            "formula": "P_so(1,3)(L^{-1} E_L[S_path])=0",
            "uses_same_l": True,
            "substituted": False,
            "blocker": "full tensor E_L[S_path] is not yet derived",
        },
        {
            "slot": "coordinate_bridge",
            "formula": "M_{-to+}=e_plus L_{-to+} e_minus^{-1}",
            "uses_same_l": True,
            "substituted": True,
            "blocker": "requires selected tetrads and selected L branch before physics closure",
        },
        {
            "slot": "k_stress_transport",
            "formula": "K_plus=M_{-to+} M_{-to+} T_minus; K_minus=M_{+to-} M_{+to-} T_plus",
            "uses_same_l": True,
            "substituted": True,
            "blocker": "divergence residuals R_plus/R_minus remain open",
        },
        {
            "slot": "qcross_optical_projection",
            "formula": "Q_cross=(eta_AB (L u_minus)^A k_plus^B)^2/(eta_AB u_plus^A k_plus^B)^2",
            "uses_same_l": True,
            "substituted": True,
            "blocker": "optical contraction is not a scalar repair for K or Bianchi residuals",
        },
        {
            "slot": "vlasov_moment_transport",
            "formula": "p_{-to+}=L p_minus; moments integrate f_minus over the same pushed momenta",
            "uses_same_l": True,
            "substituted": True,
            "blocker": "phase-space measure and kinetic hierarchy remain open",
        },
        {
            "slot": "mirror_inverse",
            "formula": "L_{+to-}=L_{-to+}^{-1}",
            "uses_same_l": True,
            "substituted": False,
            "blocker": "mirror inverse must be proved for the selected S_path branch",
        },
    ]
    forbidden_rows = [
        "do not derive K from M(L1) and Q_cross from L2",
        "do not replace the tensor bridge by scalar Q_cross",
        "do not absorb L residuals into Q_det or B4vol",
        "do not use Vlasov moments with a separate momentum bridge",
        "do not promote the extension while mirror inverse or R_plus/R_minus is open",
    ]
    return {
        "description": (
            "Same-L substitution gate for the explicit S_path extension. It fixes "
            "the contract that one selected L must generate M, K, Q_cross, Vlasov "
            "moments and mirror transport."
        ),
        "status": "spath-same-l-substitution-contract-open",
        "depends_on": [
            "p0_route_c_spath_lorentz_tetrad_variation_gate",
            "p0_same_l_bridge_induces_m_k_qcross_gate",
            "p0_l_k_qcross_consistency_target",
        ],
        "spath_lorentz_status": spath_lorentz["status"],
        "same_l_bridge_status": same_l_bridge["status"],
        "l_k_qcross_status": l_k_qcross["status"],
        "substitution_rows": substitution_rows,
        "forbidden_rows": forbidden_rows,
        "same_l_substitution_contract_written": True,
        "same_l_algebraic_stack_consistent": bool(same_l_bridge["same_l_stack_algebra_closed"]),
        "lorentz_variation_formalized": bool(spath_lorentz["lorentz_constrained_variation_formalized"]),
        "all_slots_require_same_l": all(row["uses_same_l"] for row in substitution_rows),
        "induced_m_substitution_written": True,
        "induced_k_substitution_written": True,
        "qcross_substitution_written": True,
        "vlasov_substitution_written": True,
        "mirror_inverse_substitution_closed": False,
        "full_tensor_el_closed": bool(spath_lorentz["full_tensor_el_closed"]),
        "l_selected_by_spath_el": False,
        "same_l_stack_physics_closed": False,
        "bianchi_residuals_closed": False,
        "kinetic_measure_closed": False,
        "scalar_absorption_allowed": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The same-L substitution contract is explicit: if S_path selects an L, "
            "that same L must induce M, K, Q_cross, Vlasov moments and mirror "
            "transport. This closes no physics yet because the tensor E_L, mirror "
            "inverse, kinetic measure and Bianchi residuals are still open."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Route C S_path Same-L Substitution Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Same-L substitution contract written: {payload['same_l_substitution_contract_written']}",
        f"Same-L algebraic stack consistent: {payload['same_l_algebraic_stack_consistent']}",
        f"Lorentz variation formalized: {payload['lorentz_variation_formalized']}",
        f"All slots require same L: {payload['all_slots_require_same_l']}",
        f"Mirror inverse substitution closed: {payload['mirror_inverse_substitution_closed']}",
        f"Full tensor EL closed: {payload['full_tensor_el_closed']}",
        f"L selected by S_path EL: {payload['l_selected_by_spath_el']}",
        f"Same-L stack physics closed: {payload['same_l_stack_physics_closed']}",
        f"Bianchi residuals closed: {payload['bianchi_residuals_closed']}",
        f"Kinetic measure closed: {payload['kinetic_measure_closed']}",
        f"Scalar absorption allowed: {payload['scalar_absorption_allowed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| slot | formula | uses same L | substituted | blocker |",
        "|---|---|---:|---:|---|",
    ]
    for row in payload["substitution_rows"]:
        lines.append(
            f"| {row['slot']} | `{row['formula']}` | {row['uses_same_l']} | "
            f"{row['substituted']} | {row['blocker']} |"
        )
    lines.extend(["", "## Forbidden", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_rows"])
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
