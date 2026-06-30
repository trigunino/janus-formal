from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_nonlocal_kernel_scouple_selector_obstruction.md")
JSON_PATH = Path("outputs/reports/p0_nonlocal_kernel_scouple_selector_obstruction.json")


def build_payload() -> dict:
    phi1, phi2, f1, f2 = sp.symbols("phi1 phi2 f1 f2")
    phi = sp.Matrix([phi1, phi2])
    target = sp.Matrix([f1, f2])
    invertible_kernel = sp.Matrix([[2, 1], [1, 2]])
    null_kernel = sp.Matrix([[1, -1], [-1, 1]])

    invertible_el = sp.simplify(invertible_kernel * (phi - target))
    invertible_solution = sp.solve(list(invertible_el), [phi1, phi2], dict=True)
    null_el = sp.simplify(null_kernel * (phi - target))
    null_rank = int(null_kernel.rank())
    nullity = len(null_kernel.nullspace())

    rows = [
        {
            "route": "invertible_nonlocal_kernel",
            "functional": "1/2 (phi-f)^T K (phi-f), det(K)!=0",
            "euler_lagrange": str(invertible_el),
            "selects_given_target": True,
            "source_derived_selector": False,
            "reason": "selects phi=f, but f is arbitrary unless supplied by Janus",
        },
        {
            "route": "kernel_with_zero_mode",
            "functional": "1/2 (phi-f)^T K0 (phi-f), rank(K0)<2",
            "euler_lagrange": str(null_el),
            "selects_given_target": False,
            "source_derived_selector": False,
            "reason": "zero mode leaves homogeneous freedom even after a target is specified",
        },
        {
            "route": "green_kernel_inverse_operator",
            "functional": "nonlocal Green kernel equivalent to inverse PDE operator",
            "euler_lagrange": "G^{-1}(phi-f)=0 when inverse exists",
            "selects_given_target": True,
            "source_derived_selector": False,
            "reason": "reduces to source-derived operator plus boundary/causal prescription",
        },
    ]
    return {
        "description": "Obstruction for nonlocal/history-kernel S_couple selector routes.",
        "status": "nonlocal-kernel-scouple-selector-obstruction-open",
        "invertible_kernel": str(invertible_kernel),
        "invertible_kernel_determinant": str(invertible_kernel.det()),
        "invertible_el": str(invertible_el),
        "invertible_solution": str(invertible_solution),
        "null_kernel": str(null_kernel),
        "null_kernel_rank": null_rank,
        "null_kernel_nullity": nullity,
        "null_el": str(null_el),
        "rows": rows,
        "nonlocal_kernel_can_select_given_target": True,
        "arbitrary_target_hiding_risk": True,
        "null_kernel_zero_mode_exists": bool(nullity > 0),
        "kernel_source_derived": False,
        "target_source_derived": False,
        "causal_boundary_prescription_source_derived": False,
        "nonlocal_route_selects_source_derived_phi_j_l": False,
        "requires_source_kernel": True,
        "requires_source_target_or_current": True,
        "requires_causal_boundary_prescription": True,
        "requires_mirror_inverse_proof": True,
        "requires_same_l_tensor_residual_proof": True,
        "requires_split_noether_proof": True,
        "new_axiom_if_adopted_without_source": True,
        "uses_observational_fit": False,
        "uses_qdet_qcross_absorption": False,
        "hidden_axiom_used": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "A nonlocal kernel can select a map only after a kernel, target/current, "
            "and causal or boundary prescription are supplied. Without Janus provenance, "
            "that power is exactly the risk: the kernel can encode the desired phi/J/L "
            "as a hidden axiom."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Nonlocal Kernel S_couple Selector Obstruction",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Invertible kernel: `{payload['invertible_kernel']}`",
        f"Invertible kernel determinant: `{payload['invertible_kernel_determinant']}`",
        f"Invertible EL: `{payload['invertible_el']}`",
        f"Invertible solution: `{payload['invertible_solution']}`",
        f"Null kernel rank: {payload['null_kernel_rank']}",
        f"Null kernel nullity: {payload['null_kernel_nullity']}",
        f"Nonlocal kernel can select given target: {payload['nonlocal_kernel_can_select_given_target']}",
        f"Arbitrary target hiding risk: {payload['arbitrary_target_hiding_risk']}",
        f"Null kernel zero mode exists: {payload['null_kernel_zero_mode_exists']}",
        f"Kernel source derived: {payload['kernel_source_derived']}",
        f"Target source derived: {payload['target_source_derived']}",
        (
            "Causal boundary prescription source derived: "
            f"{payload['causal_boundary_prescription_source_derived']}"
        ),
        (
            "Nonlocal route selects source-derived phi/J/L: "
            f"{payload['nonlocal_route_selects_source_derived_phi_j_l']}"
        ),
        f"Requires source kernel: {payload['requires_source_kernel']}",
        f"Requires source target/current: {payload['requires_source_target_or_current']}",
        f"Requires causal boundary prescription: {payload['requires_causal_boundary_prescription']}",
        f"Requires mirror inverse proof: {payload['requires_mirror_inverse_proof']}",
        f"Requires same-L tensor residual proof: {payload['requires_same_l_tensor_residual_proof']}",
        f"Requires split Noether proof: {payload['requires_split_noether_proof']}",
        f"New axiom if adopted without source: {payload['new_axiom_if_adopted_without_source']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Uses Qdet/Qcross absorption: {payload['uses_qdet_qcross_absorption']}",
        f"Hidden axiom used: {payload['hidden_axiom_used']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Rows",
        "",
        "| route | functional | Euler-Lagrange | selects target | source-derived selector | reason |",
        "|---|---|---|---:|---:|---|",
    ]
    for row in payload["rows"]:
        lines.append(
            f"| {row['route']} | `{row['functional']}` | `{row['euler_lagrange']}` | "
            f"{row['selects_given_target']} | {row['source_derived_selector']} | {row['reason']} |"
        )
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
