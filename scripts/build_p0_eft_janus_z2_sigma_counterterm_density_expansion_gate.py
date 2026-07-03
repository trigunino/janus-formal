from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_density_expansion_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_counterterm_density_expansion_gate.json")


def build_payload() -> dict:
    declared = {
        "Sigma_counterterm_uniqueness_imported": True,
        "counterterm_cancels_nonlinear_residual_imported": True,
        "density_expansion_problem_declared": True,
        "allowed_variables_declared": True,
        "no_new_counterterm_freedom_declared": True,
        "observational_fit_forbidden": True,
        "explicit_density_expansion_required": True,
    }
    closure = {
        "L_ct_expanded_in_active_variables": False,
        "L_ct_uniqueness_preserved": False,
        "L_ct_ready_for_radial_variation": False,
    }
    return {
        "status": "janus-z2-sigma-counterterm-density-expansion-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "active Janus Sigma nonlinear residual closure gate",
            "Brown-York boundary counterterm stress method",
            "boundary counterterm renormalization literature",
        ],
        "bibliography_result": (
            "The active repository proves uniqueness/cancellation of the Sigma counterterm, "
            "while generic literature supplies variation methods. No external source expands "
            "the active Janus/Sigma counterterm density in local radial variables."
        ),
        "declared": declared,
        "closure": closure,
        "allowed_variables": [
            "h_ab",
            "K_ab",
            "Sigma torsion pullback",
            "Immirzi/radion boundary fields",
            "Z2 orientation sign",
        ],
        "forbidden": [
            "new fitted counterterm coefficient",
            "observational radius fit",
            "legacy Z4 counterterm import",
        ],
        "counterterm_density_expansion_ledger_declared": all(declared.values()),
        "counterterm_density_expansion_ready": all(declared.values()) and all(closure.values()),
        "next_required": [
            "expand_L_ct_in_h_K_torsion_Immirzi_variables",
            "prove_expansion_preserves_unique_residual_cancellation",
            "pass_L_ct_to_counterterm_radial_block",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm Density Expansion Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['counterterm_density_expansion_ledger_declared']}`",
        f"Expansion ready: `{payload['counterterm_density_expansion_ready']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
