from __future__ import annotations

from pathlib import Path
import json

try:
    from scripts.build_p0_eft_active_stress_alpha_derivation import build_payload as build_alpha_payload
    from scripts.build_p0_eft_growth_kink_mu_functions import build_payload as build_kink_mu_payload
    from scripts.build_p0_eft_slip_jump_derivation_check import build_payload as build_jump_payload
    from scripts.build_p0_eft_spinless_isotropic_alpha_branch import build_payload as build_alpha_iso_payload
except ModuleNotFoundError:
    from build_p0_eft_active_stress_alpha_derivation import build_payload as build_alpha_payload
    from build_p0_eft_growth_kink_mu_functions import build_payload as build_kink_mu_payload
    from build_p0_eft_slip_jump_derivation_check import build_payload as build_jump_payload
    from build_p0_eft_spinless_isotropic_alpha_branch import build_payload as build_alpha_iso_payload


REPORT_PATH = Path("outputs/reports/p0_eft_kink_source_closure_audit.md")
JSON_PATH = Path("outputs/reports/p0_eft_kink_source_closure_audit.json")


def build_payload() -> dict:
    jump = build_jump_payload()
    kink_mu = build_kink_mu_payload()
    alpha = build_alpha_payload()
    alpha_iso = build_alpha_iso_payload()
    status = {
        "derivative_jump_source_closed": jump["theorem_status"]["derivative_jump_slip_source_closed"],
        "skink_formula_encoded": kink_mu["theorem_status"]["skink_formula_encoded"],
        "skink_coefficient_derived": kink_mu["theorem_status"]["skink_coefficient_derived"],
        "alpha_definition_encoded": alpha["theorem_status"]["alpha_definition_encoded"],
        "alpha_iso_formula_encoded": alpha_iso["theorem_status"]["alpha_iso_formula_encoded"],
        "alpha_iso_fully_derived": alpha_iso["theorem_status"]["alpha_iso_fully_derived"],
        "alpha_Janus_derived": alpha["theorem_status"]["alpha_Janus_derived"],
        "kink_source_promotable": False,
        "prediction_ready_unconditional": False,
    }
    blockers = [
        "exact Euler/geodesic projection coefficient from Delta(partial_n(Psi-Phi)) to S_kink",
        "normalization of rho_torsion_eff in alpha_iso(a)",
        "general Pi branch or explicit isotropic-domain restriction",
    ]
    return {
        "description": "Closure audit for the Janus-Holst kink source factors S_kink and alpha_Janus(a).",
        "status": "kink-source-closure-open",
        "factorization": "Delta(delta') = S_kink(k,a_sigma) * alpha_Janus(a_sigma) * delta(a_sigma)",
        "closed_piece": "derivative jump source structure",
        "conditional_piece": "spinless isotropic alpha shape alpha_iso(a) proportional to (7/6)*Omega_torsion(a)",
        "open_blockers": blockers,
        "theorem_status": status,
        "verdict": "Do not promote to KiDS prediction until S_kink coefficient and alpha normalization are source-derived.",
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Kink Source Closure Audit",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Factorization: {payload['factorization']}",
        f"Closed piece: {payload['closed_piece']}",
        f"Conditional piece: {payload['conditional_piece']}",
        "",
        "## Status",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["theorem_status"].items())
    lines.extend(["", "## Open Blockers"])
    lines.extend(f"- {item}" for item in payload["open_blockers"])
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
