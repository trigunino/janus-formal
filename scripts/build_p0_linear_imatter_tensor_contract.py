from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_linear_imatter_tensor_contract.md")
JSON_PATH = Path("outputs/reports/p0_linear_imatter_tensor_contract.json")


def build_payload() -> dict:
    contracts = [
        {
            "name": "plus_view",
            "formula": "I_matter_plus = T_plus^{mu nu} (L T_minus L^T)_{mu nu}",
            "role": "linear cross-matter scalar in the plus variation",
        },
        {
            "name": "minus_view",
            "formula": "I_matter_minus = T_minus^{ab} (L^{-1} T_plus L^{-T})_{ab}",
            "role": "mirror scalar in the minus variation",
        },
        {
            "name": "dust_limit",
            "formula": "T_s^{mu nu}=rho_s u_s^mu u_s^nu gives I_matter ~ rho_plus rho_minus (u_plus.u_minus_to_plus)^2",
            "role": "connects tensor contraction to Q_cross-like velocity projection",
        },
    ]
    variation_requirements = [
        "metric variation must include explicit index raising/lowering convention",
        "volume-measure trace is available but is not the full K tensor",
        "L variation must include delta(L T_minus L^T)",
        "phi variation must include pullback of T_minus and density support",
        "pressure/Pi terms must be kept when T is not dust",
    ]
    return {
        "description": "Tensor contract for the linear I_matter candidate used by Split Noether.",
        "status": "tensor-contract-defined-variation-open",
        "contracts": contracts,
        "variation_requirements": variation_requirements,
        "imatter_tensor_contract_defined": True,
        "dust_projection_bridge_available": True,
        "metric_measure_variation_available": True,
        "metric_variation_closed": False,
        "l_variation_algebra_closed": True,
        "lorentz_projected_e_l_closed": True,
        "map_l_variation_closed": False,
        "pressure_pi_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "I_matter is now a concrete tensor contraction rather than an abstract scalar. "
            "Split Noether still requires explicit metric, L, and phi variations."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Linear I_matter Tensor Contract",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"I_matter tensor contract defined: {payload['imatter_tensor_contract_defined']}",
        f"Dust projection bridge available: {payload['dust_projection_bridge_available']}",
        f"Metric measure variation available: {payload['metric_measure_variation_available']}",
        f"Metric variation closed: {payload['metric_variation_closed']}",
        f"L variation algebra closed: {payload['l_variation_algebra_closed']}",
        f"Lorentz projected E_L closed: {payload['lorentz_projected_e_l_closed']}",
        f"Map/L variation closed: {payload['map_l_variation_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Contracts",
        "",
    ]
    for row in payload["contracts"]:
        lines.append(f"- {row['name']}: `{row['formula']}`")
        lines.append(f"  - role: {row['role']}")
    lines.extend(["", "## Variation Requirements", ""])
    lines.extend(f"- {item}" for item in payload["variation_requirements"])
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
