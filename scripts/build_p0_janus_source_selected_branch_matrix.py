from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_janus_source_selected_branch_matrix.md")
JSON_PATH = Path("outputs/reports/p0_janus_source_selected_branch_matrix.json")


def build_payload() -> dict:
    branches = [
        {
            "branch": "qdet_density_convention",
            "source_anchor": "M15 Eqs. 4a-4b cross-source determinant slots",
            "selected": "conditional",
            "selection": "positive_effective_density uses q_det=1 after B_4vol has already weighted the active source",
            "forbidden": "negative_proper_density multiplied by B_4vol twice or raw (a_minus/a_plus)^4 lensing amplitude",
        },
        {
            "branch": "background_zero_mode",
            "source_anchor": "conditional dust/slip k=0 compatibility",
            "selected": "not-global",
            "selection": "source compatibility must hold before fixing common potential gauge",
            "forbidden": "using the common zero mode as a fitted lensing or sigma8 amplitude",
        },
        {
            "branch": "boundary_gauge",
            "source_anchor": "Poisson/Fourier weak-field operator",
            "selected": "diagnostic-only",
            "selection": "periodic diagnostic branch may set mean(Psi_plus+Psi_minus)=0 after compatibility",
            "forbidden": "promoting periodic mean-zero gauge to a physical Janus boundary law",
        },
        {
            "branch": "same_l_for_k_qcross",
            "source_anchor": "Q_cross tetrad-map target plus Bianchi K transport gate",
            "selected": "partial-derived",
            "selection": "FLRW/comoving scalar weak-field branch selects L=I because eta-skew(L_geom-I)=0; non-comoving shift branch derives F_i0=Delta_B_i/2 and G0i shift operator, but still needs transported T0i matter closure",
            "forbidden": "using one L for Q_cross and another transport for K_plus/K_minus",
        },
    ]
    return {
        "description": "Matrix of what Janus source equations currently select for weak-field P0 branches.",
        "status": "source-selected-branch-matrix-open",
        "source_anchors": [
            "M15 coupled field equations with determinant-weighted cross-source terms",
            "M30 Newtonian effective-density convention as local diagnostic support",
            "local tetrad/Q_cross algebra requiring the same L as K transport",
        ],
        "branches": branches,
        "qdet_branch_conditionally_selected": True,
        "background_zero_mode_globally_selected": False,
        "boundary_gauge_physically_selected": False,
        "same_l_global_perturbed_branch_selected": False,
        "flrw_comoving_same_l_identity_selected": True,
        "weakfield_scalar_lorentz_projection_selected_identity": True,
        "weakfield_shift_boost_projection_derived": True,
        "janus_0i_shift_source_operator_closed": True,
        "pressure_pi0i_transport_closed": False,
        "uses_observational_fit": False,
        "uses_scalar_absorption": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "Janus source slots select the determinant-density bookkeeping, and FLRW comoving "
            "algebra selects L=I in that special branch. The global background/gauge and "
            "perturbed same-L branches remain open and must not be filled by fits."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Source-Selected Branch Matrix",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Q_det branch conditionally selected: {payload['qdet_branch_conditionally_selected']}",
        f"Background zero mode globally selected: {payload['background_zero_mode_globally_selected']}",
        f"Boundary/gauge physically selected: {payload['boundary_gauge_physically_selected']}",
        f"Same-L global perturbed branch selected: {payload['same_l_global_perturbed_branch_selected']}",
        f"FLRW comoving same-L identity selected: {payload['flrw_comoving_same_l_identity_selected']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Uses scalar absorption: {payload['uses_scalar_absorption']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Source Anchors",
        "",
    ]
    lines.extend(f"- {item}" for item in payload["source_anchors"])
    lines.extend(["", "## Branches", "", "| branch | source anchor | selected | selection | forbidden |", "|---|---|---|---|---|"])
    for row in payload["branches"]:
        lines.append(
            f"| {row['branch']} | {row['source_anchor']} | {row['selected']} | "
            f"{row['selection']} | {row['forbidden']} |"
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
