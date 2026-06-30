from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_b4vol_jacobian_gauge_degeneracy_proof.md")
JSON_PATH = Path("outputs/reports/p0_b4vol_jacobian_gauge_degeneracy_proof.json")


def build_payload() -> dict:
    j_phi, slice_ratio, lam = sp.symbols("J_phi S_slice lambda", positive=True)
    dlog_j, dlog_s, dlam = sp.symbols("DlogJ DlogS Dlambda")

    b4vol = j_phi * slice_ratio
    transformed_b4vol = sp.simplify(j_phi * sp.exp(lam) * slice_ratio * sp.exp(-lam))
    dlog_original = dlog_j + dlog_s
    dlog_shifted = (dlog_j + dlam) + (dlog_s - dlam)

    rows = [
        {
            "identity": "b4vol_factorization",
            "formula": "B4vol = J_phi * S_slice",
            "closed": True,
            "meaning": "source equations can fix the product without fixing each factor",
        },
        {
            "identity": "multiplicative_gauge_family",
            "formula": "J_phi -> exp(lambda) J_phi, S_slice -> exp(-lambda) S_slice",
            "closed": bool(sp.simplify(transformed_b4vol - b4vol) == 0),
            "meaning": "there is an infinite family with the same B4vol",
        },
        {
            "identity": "dlog_family",
            "formula": "DlogJ -> DlogJ + Dlambda, DlogS -> DlogS - Dlambda",
            "closed": bool(sp.simplify(dlog_shifted - dlog_original) == 0),
            "meaning": "D log B4vol cannot isolate D log J_phi without a slice/lapse selector",
        },
    ]
    return {
        "description": "Symbolic proof that B4vol alone underselects J_phi in the general branch.",
        "status": "b4vol-jacobian-gauge-degeneracy-proved",
        "b4vol_formula": str(b4vol),
        "transformed_b4vol": str(transformed_b4vol),
        "dlog_original": str(dlog_original),
        "dlog_shifted": str(dlog_shifted),
        "rows": rows,
        "degeneracy_symbolic_identity_closed": all(row["closed"] for row in rows),
        "source_b4vol_alone_selects_jphi": False,
        "requires_slice_lapse_selector": True,
        "flrw_fixed_slice_conditional_selects_jphi": True,
        "general_perturbed_jphi_selected": False,
        "uses_observational_fit": False,
        "uses_qdet_qcross_absorption": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The product B4vol is invariant under a compensating rescaling of "
            "J_phi and the slice/lapse factor. Therefore a source identity for "
            "B4vol is not enough to select J_phi in the general perturbed branch."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 B4vol/Jacobian Gauge Degeneracy Proof",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"B4vol formula: `{payload['b4vol_formula']}`",
        f"Transformed B4vol: `{payload['transformed_b4vol']}`",
        f"Dlog original: `{payload['dlog_original']}`",
        f"Dlog shifted: `{payload['dlog_shifted']}`",
        f"Degeneracy identity closed: {payload['degeneracy_symbolic_identity_closed']}",
        f"Source B4vol alone selects J_phi: {payload['source_b4vol_alone_selects_jphi']}",
        f"Requires slice/lapse selector: {payload['requires_slice_lapse_selector']}",
        f"FLRW fixed-slice conditional selects J_phi: {payload['flrw_fixed_slice_conditional_selects_jphi']}",
        f"General perturbed J_phi selected: {payload['general_perturbed_jphi_selected']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Uses Qdet/Qcross absorption: {payload['uses_qdet_qcross_absorption']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Identities",
        "",
        "| identity | formula | closed | meaning |",
        "|---|---|---:|---|",
    ]
    for row in payload["rows"]:
        lines.append(
            f"| {row['identity']} | `{row['formula']}` | "
            f"{row['closed']} | {row['meaning']} |"
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
