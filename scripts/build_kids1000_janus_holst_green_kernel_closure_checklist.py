from __future__ import annotations

from pathlib import Path
import json

try:
    from scripts.build_kids1000_janus_holst_value_slip_scaffold import build_payload as build_scaffold_payload
    from scripts.build_p0_eft_dS3_green_kernel_audit import build_payload as build_ds3_payload
    from scripts.build_p0_eft_ds3_projected_green_calculation import build_payload as build_projected_green_payload
    from scripts.build_p0_eft_slip_green_neumann_bridge import build_payload as build_neumann_payload
    from scripts.build_p0_janus_weakfield_dust_slip_green_kernel_target import build_payload as build_dust_green_payload
except ModuleNotFoundError:
    from build_kids1000_janus_holst_value_slip_scaffold import build_payload as build_scaffold_payload
    from build_p0_eft_dS3_green_kernel_audit import build_payload as build_ds3_payload
    from build_p0_eft_ds3_projected_green_calculation import build_payload as build_projected_green_payload
    from build_p0_eft_slip_green_neumann_bridge import build_payload as build_neumann_payload
    from build_p0_janus_weakfield_dust_slip_green_kernel_target import build_payload as build_dust_green_payload


REPORT_PATH = Path("outputs/reports/kids1000_janus_holst_green_kernel_closure_checklist.md")
JSON_PATH = Path("outputs/reports/kids1000_janus_holst_green_kernel_closure_checklist.json")


def checklist_rows(
    scaffold: dict,
    neumann: dict,
    dust_green: dict,
    ds3: dict | None = None,
    projected_green: dict | None = None,
) -> list[dict]:
    ds3_status = ds3["theorem_status"] if ds3 else {}
    return [
        {
            "check": "boundary_operator_specified",
            "passed": bool(neumann["theorem_status"]["target_kernel_identified"]),
            "blocker": "specify the boundary operator that defines G_Neumann^Sigma",
        },
        {
            "check": "boundary_conditions_source_derived",
            "passed": bool(dust_green["boundary_conditions_source_derived"]),
            "blocker": "derive boundary conditions from Janus-Holst source, not survey residuals",
        },
        {
            "check": "zero_mode_policy_fixed",
            "passed": bool(dust_green["zero_mode_policy_written"]),
            "blocker": "write compatible zero-mode policy",
        },
        {
            "check": "finite_mode_green_kernel_computed",
            "passed": bool(neumann["theorem_status"]["green_kernel_computed"]),
            "blocker": "compute the finite-mode Neumann Green kernel",
        },
        {
            "check": "ds3_renormalized_response_proved",
            "passed": bool(ds3_status.get("green_kernel_equals_three_halves_H_proved", False)),
            "blocker": "prove or replace the renormalized dS3 response G_Neumann^Sigma=(3/2)H",
        },
        {
            "check": "projected_green_scheme_fixed",
            "passed": bool(projected_green and not projected_green["scheme_dependent"]),
            "blocker": "fix a source-derived projection/renormalization scheme for the dS3 Green response",
        },
        {
            "check": "normalization_not_kids_fitted",
            "passed": not bool(scaffold["uses_kids_residuals"])
            and not bool(scaffold["uses_delta_z"])
            and not bool(scaffold["uses_bin_factors"]),
            "blocker": "remove KiDS residual, delta_z or bin-factor inputs",
        },
        {
            "check": "eta_slip_finite_on_kids_lens_grid",
            "passed": bool(scaffold["green_kernel_computed"]),
            "blocker": "evaluate finite eta_slip_JH(k,a) after the Green kernel is computed",
        },
        {
            "check": "qdet_and_qcross_source_selected",
            "passed": bool(dust_green["qdet_convention_selected_from_source"])
            and bool(dust_green["same_l_qcross_selected"]),
            "blocker": "select Q_det and same-L/Q_cross conventions from source",
        },
    ]


def build_payload() -> dict:
    scaffold = build_scaffold_payload()
    neumann = build_neumann_payload()
    dust_green = build_dust_green_payload()
    ds3 = build_ds3_payload()
    projected_green = build_projected_green_payload()
    rows = checklist_rows(scaffold, neumann, dust_green, ds3, projected_green)
    blockers = [row["blocker"] for row in rows if not row["passed"]]
    return {
        "description": "Closure checklist before enabling the KiDS-1000 Janus-Holst value-slip Green kernel.",
        "status": "green-kernel-closure-checklist-open",
        "checks": rows,
        "found_derivation_status": {
            "jump_derivation": "derivative slip source closed",
            "neumann_bridge": neumann["status"],
            "ds3_audit": ds3["status"],
            "projected_green_calculation": projected_green["status"],
            "complete_value_derivation_found": False,
        },
        "blockers": blockers,
        "green_kernel_computed": False,
        "can_enable_value_slip": len(blockers) == 0,
        "prediction_ready": False,
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# KiDS-1000 Janus-Holst Green-Kernel Closure Checklist",
        "",
        payload["description"],
        "",
        f"Status: `{payload['status']}`",
        f"Green kernel computed: `{payload['green_kernel_computed']}`",
        f"Can enable value slip: `{payload['can_enable_value_slip']}`",
        f"Prediction ready: `{payload['prediction_ready']}`",
        "",
        "| check | passed | blocker |",
        "|---|---:|---|",
    ]
    for row in payload["checks"]:
        lines.append(f"| {row['check']} | {row['passed']} | {row['blocker']} |")
    lines.extend(["", "## Blockers", ""])
    lines.extend(f"- {item}" for item in payload["blockers"])
    lines.append("")
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
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
