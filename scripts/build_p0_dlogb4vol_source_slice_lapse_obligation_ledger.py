from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_dlogb4vol_jacobian_lapse_slice_identity_target import (
    build_payload as build_jacobian_lapse_slice,
)


REPORT_PATH = Path("outputs/reports/p0_dlogb4vol_source_slice_lapse_obligation_ledger.md")
JSON_PATH = Path("outputs/reports/p0_dlogb4vol_source_slice_lapse_obligation_ledger.json")


def build_payload() -> dict:
    jacobian_lapse_slice = build_jacobian_lapse_slice()
    obligation_rows = [
        {
            "id": "B4-SRC-PLUS",
            "sector": "plus",
            "product_rule_term": "D_plus log B_4vol_plus_from_minus",
            "required_identity_type": "source-determinant",
            "required_identity": "D_plus log sqrt(-g_minus) - D_plus log sqrt(-g_plus)",
            "source_anchor": "M15/M30 determinant-weighted cross-source layer",
            "blocks": "R_plus product-rule cancellation",
            "closed": False,
        },
        {
            "id": "B4-SLICE-PLUS",
            "sector": "plus",
            "product_rule_term": "D_plus log gamma_minus/gamma_plus",
            "required_identity_type": "slice-determinant",
            "required_identity": "receiver derivative of the source/receiver spatial determinant ratio",
            "source_anchor": "p0_dlogb_4volume_obstruction",
            "blocks": "R_plus B4vol/V3_dust separation",
            "closed": False,
        },
        {
            "id": "B4-LAPSE-PLUS",
            "sector": "plus",
            "product_rule_term": "D_plus log N_minus/N_plus",
            "required_identity_type": "lapse-reinsertion",
            "required_identity": "proof when dust 3-volume law may be lifted to four-volume law",
            "source_anchor": "p0_dlogb4vol_measure_law_derivation_attempt",
            "blocks": "R_plus lapse-bearing source density",
            "closed": False,
        },
        {
            "id": "B4-DENSITY",
            "sector": "both",
            "product_rule_term": "D_receiver(B_4vol rho_to u_to)",
            "required_identity_type": "density-transport",
            "required_identity": "transported density law using the same source measure as field equations",
            "source_anchor": "p0_b4vol_janus_source_anchor",
            "blocks": "density rows in R_plus/R_minus",
            "closed": False,
        },
        {
            "id": "B4-VEL-TETRAD",
            "sector": "both",
            "product_rule_term": "D_receiver u_to and D_receiver tetrad rows",
            "required_identity_type": "velocity-tetrad",
            "required_identity": "same velocity/tetrad map used by B4vol, L, and Cuu rows",
            "source_anchor": "p0_janus_phase_space_b4vol_measure_gate",
            "blocks": "velocity/tetrad rows in R_plus/R_minus",
            "closed": False,
        },
        {
            "id": "B4-MIRROR",
            "sector": "minus",
            "product_rule_term": "D_minus log B_4vol_minus_from_plus",
            "required_identity_type": "mirror-reciprocity",
            "required_identity": "plus_from_minus and minus_from_plus determinant derivatives are reciprocal under the accepted map",
            "source_anchor": "p0_janus_equations_to_dlogb4vol_closure_attempt",
            "blocks": "R_minus mirror product-rule cancellation",
            "closed": False,
        },
        {
            "id": "B4-JAC-LAPSE-SLICE",
            "sector": "both",
            "product_rule_term": "D_receiver log B_4vol decomposition",
            "required_identity_type": "jacobian-lapse-slice",
            "required_identity": "D log B_4vol = D log J_phi + D log lapse ratio + D log slice ratio",
            "source_anchor": "p0_dlogb4vol_jacobian_lapse_slice_identity_target",
            "blocks": "using one B4vol convention in R_plus/R_minus",
            "closed": jacobian_lapse_slice["source_selected_measure_found"],
        },
    ]
    forbidden_operations = [
        "no Q_det absorption of D log B_4vol rows",
        "no Q_cross absorption of D log B_4vol rows",
        "no B_4vol/V3_dust conflation",
        "no closure claim from conditional branch selection alone",
    ]
    return {
        "description": "Source/slice/lapse obligation ledger for D log B_4vol closure.",
        "status": "source-slice-lapse-obligation-ledger-open",
        "depends_on": [
            "p0_janus_weakfield_b4vol_product_rule_probe",
            "p0_dlogb4vol_measure_law_derivation_attempt",
            "p0_janus_equations_to_dlogb4vol_closure_attempt",
            "p0_b4vol_janus_source_anchor",
            "p0_dlogb4vol_jacobian_lapse_slice_identity_target",
        ],
        "obligation_rows": obligation_rows,
        "forbidden_operations": forbidden_operations,
        "diagnostic_product_rule_only": True,
        "jacobian_lapse_slice_identity_written": jacobian_lapse_slice["identity_written"],
        "jacobian_lapse_slice_identity_numeric_closes": jacobian_lapse_slice["identity_numeric_closes"],
        "mirror_reciprocity_numeric_closes": jacobian_lapse_slice["mirror_reciprocity_numeric_closes"],
        "source_selected_measure_found": jacobian_lapse_slice["source_selected_measure_found"],
        "source_slice_lapse_obligations_closed": False,
        "qdet_qcross_absorption_forbidden": True,
        "b4vol_v3_dust_conflation_forbidden": True,
        "branch_selection_is_not_closure": True,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "D log B_4vol is localized to source, slice, lapse, density, velocity/tetrad, "
            "and mirror reciprocity obligations. None is closed by the diagnostic product rule."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 DlogB4vol Source/Slice/Lapse Obligation Ledger",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Diagnostic product rule only: {payload['diagnostic_product_rule_only']}",
        f"Jacobian/lapse/slice identity written: {payload['jacobian_lapse_slice_identity_written']}",
        f"Jacobian/lapse/slice identity numeric closes: {payload['jacobian_lapse_slice_identity_numeric_closes']}",
        f"Mirror reciprocity numeric closes: {payload['mirror_reciprocity_numeric_closes']}",
        f"Source-selected measure found: {payload['source_selected_measure_found']}",
        f"Source/slice/lapse obligations closed: {payload['source_slice_lapse_obligations_closed']}",
        f"Q_det/Q_cross absorption forbidden: {payload['qdet_qcross_absorption_forbidden']}",
        f"B4vol/V3_dust conflation forbidden: {payload['b4vol_v3_dust_conflation_forbidden']}",
        f"Branch selection is not closure: {payload['branch_selection_is_not_closure']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Obligations",
        "",
        "| id | sector | type | product-rule term | blocks | closed |",
        "|---|---|---|---|---|---:|",
    ]
    for row in payload["obligation_rows"]:
        lines.append(
            f"| {row['id']} | {row['sector']} | {row['required_identity_type']} | "
            f"{row['product_rule_term']} | {row['blocks']} | {row['closed']} |"
        )
    lines.extend(["", "## Forbidden Operations", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_operations"])
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
