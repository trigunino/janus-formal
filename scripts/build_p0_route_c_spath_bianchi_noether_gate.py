from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_route_c_spath_lorentz_tetrad_variation_gate import (
    build_payload as build_spath_lorentz,
)
from scripts.build_p0_route_c_spath_same_l_substitution_gate import (
    build_payload as build_spath_same_l,
)
from scripts.build_p0_route_c_spath_stability_screen import (
    build_payload as build_spath_stability,
)
from scripts.build_p0_route_c_spath_metric_stress_variation_gate import (
    build_payload as build_metric_stress,
)


REPORT_PATH = Path("outputs/reports/p0_route_c_spath_bianchi_noether_gate.md")
JSON_PATH = Path("outputs/reports/p0_route_c_spath_bianchi_noether_gate.json")


def build_payload() -> dict:
    lorentz = build_spath_lorentz()
    same_l = build_spath_same_l()
    stability = build_spath_stability()
    metric_stress = build_metric_stress()
    noether_rows = [
        {
            "identity": "diagonal_diffeomorphism",
            "formula": "nabla_plus K_plus + transported(nabla_minus K_minus) + E_gamma D gamma + E_L D L = 0",
            "required_for_closure": "must split into R_plus=0 and R_minus=0 on shell",
            "proved": False,
            "blocker": "diagonal covariance gives one combined identity, not two sector residuals",
        },
        {
            "identity": "plus_sector_bianchi",
            "formula": "R_plus^nu = nabla_plus_mu(T_plus^{mu nu}+K_plus^{mu nu})",
            "required_for_closure": "vanishes after E_gamma=0, projected E_L=0 and same-L substitution",
            "proved": False,
            "blocker": "K_plus from metric variation of full tensor S_path is not derived",
        },
        {
            "identity": "minus_sector_bianchi",
            "formula": "R_minus^nu = nabla_minus_mu(T_minus^{mu nu}+K_minus^{mu nu})",
            "required_for_closure": "mirror residual vanishes with inverse path/L branch",
            "proved": False,
            "blocker": "mirror split identity and inverse branch are not proved",
        },
        {
            "identity": "same_l_noether_source",
            "formula": "E_L projected on so(1,3) uses the same L as K_plus, K_minus, Q_cross and Vlasov moments",
            "required_for_closure": "no independent optical or matter bridge",
            "proved": False,
            "blocker": "same-L contract is written but not source-selected",
        },
        {
            "identity": "stress_from_metric_variation",
            "formula": "K_plus/minus^{mu nu}=(-2/sqrt(-g_plus/minus)) delta S_path/delta g_plus/minus_{mu nu}",
            "required_for_closure": "pressure, Pi and boundary terms appear as tensors",
            "proved": False,
            "blocker": "current S_path terms are formal selectors, not full metric variations",
        },
    ]
    rejection_rules = [
        "do not infer R_plus=R_minus=0 from one diagonal Noether identity",
        "do not absorb E_gamma or E_L residues into scalar Q_det/Q_cross",
        "do not reuse a stable path screen as a Bianchi proof",
        "do not use a different L in stress transport and optical projection",
    ]
    return {
        "description": (
            "Bianchi/Noether acceptance gate for the explicit S_path extension. "
            "It states the tensor identities needed before S_path can be used "
            "as a physical Janus interaction rather than a selector scaffold."
        ),
        "status": "spath-bianchi-noether-gate-open",
        "depends_on": [
            "p0_route_c_spath_lorentz_tetrad_variation_gate",
            "p0_route_c_spath_same_l_substitution_gate",
            "p0_route_c_spath_stability_screen",
            "p0_route_c_spath_metric_stress_variation_gate",
        ],
        "lorentz_variation_formalized": bool(lorentz["lorentz_constrained_variation_formalized"]),
        "same_l_contract_written": bool(same_l["same_l_substitution_contract_written"]),
        "stability_screen_written": bool(stability["stability_screen_written"]),
        "metric_stress_variation_written": bool(metric_stress["hilbert_stress_definition_written"]),
        "metric_stress_variation_closed": bool(metric_stress["physics_closed"]),
        "noether_rows": noether_rows,
        "rejection_rules": rejection_rules,
        "combined_noether_identity_written": True,
        "split_noether_identities_proved": False,
        "k_plus_metric_variation_derived": False,
        "k_minus_metric_variation_derived": False,
        "same_l_noether_source_derived": False,
        "mirror_inverse_identity_proved": False,
        "pressure_pi_tensor_terms_derived": False,
        "bianchi_noether_gate_closed": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "S_path still fails the physical acceptance gate: the formal EL/Lorentz/"
            "same-L/stability pieces are useful, but no split Noether proof, metric "
            "stress variation, mirror residual, or pressure/Pi tensor derivation is closed."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Route C S_path Bianchi/Noether Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Lorentz variation formalized: {payload['lorentz_variation_formalized']}",
        f"Same-L contract written: {payload['same_l_contract_written']}",
        f"Stability screen written: {payload['stability_screen_written']}",
        f"Metric stress variation written: {payload['metric_stress_variation_written']}",
        f"Metric stress variation closed: {payload['metric_stress_variation_closed']}",
        f"Combined Noether identity written: {payload['combined_noether_identity_written']}",
        f"Split Noether identities proved: {payload['split_noether_identities_proved']}",
        f"K_plus metric variation derived: {payload['k_plus_metric_variation_derived']}",
        f"K_minus metric variation derived: {payload['k_minus_metric_variation_derived']}",
        f"Same-L Noether source derived: {payload['same_l_noether_source_derived']}",
        f"Mirror inverse identity proved: {payload['mirror_inverse_identity_proved']}",
        f"Pressure/Pi tensor terms derived: {payload['pressure_pi_tensor_terms_derived']}",
        f"Bianchi/Noether gate closed: {payload['bianchi_noether_gate_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| identity | formula | required for closure | proved | blocker |",
        "|---|---|---|---:|---|",
    ]
    for row in payload["noether_rows"]:
        lines.append(
            f"| {row['identity']} | `{row['formula']}` | "
            f"{row['required_for_closure']} | {row['proved']} | {row['blocker']} |"
        )
    lines.extend(["", "## Rejection Rules", ""])
    lines.extend(f"- {item}" for item in payload["rejection_rules"])
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
