from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_route_c_minimal_spath_extension_axiom_gate import (
    build_payload as build_minimal_spath,
)


REPORT_PATH = Path("outputs/reports/p0_route_c_spath_scalar_density_completion_gate.md")
JSON_PATH = Path("outputs/reports/p0_route_c_spath_scalar_density_completion_gate.json")


def build_payload() -> dict:
    minimal = build_minimal_spath()
    completion_rows = [
        {
            "slot": "path_measure",
            "requirement": "d lambda density is reparametrization invariant and not tied to observation",
            "candidate_form": "d lambda sqrt(abs(gamma_dot g_s gamma_dot)) or equivalent affine gauge",
            "closed": False,
            "blocker": "preferred path parameter/gauge is not source-selected",
        },
        {
            "slot": "C_J_scalar",
            "requirement": "C_J is a diagonal-diffeomorphism scalar built from Janus fields",
            "candidate_form": "C_J(I_curv,I_strain,I_PT,matter invariants)",
            "closed": False,
            "blocker": "no Janus source fixes the invariant list or coefficients",
        },
        {
            "slot": "V_J_scalar",
            "requirement": "V_J is a scalar potential selecting path branch without fit",
            "candidate_form": "V_J(I_curv,I_strain,I_PT,matter invariants)",
            "closed": False,
            "blocker": "no boundary/source law selects the branch",
        },
        {
            "slot": "lorentz_transport_scalar",
            "requirement": "D_s L term is a true scalar and uses same L as K/Q_cross/Vlasov",
            "candidate_form": "Tr_eta((D_s L)^dagger D_s L) with constrained so(1,3) projection",
            "closed": False,
            "blocker": "positive algebra norm remains gauge/source-open",
        },
        {
            "slot": "mirror_pt_parity",
            "requirement": "S_path[plus->minus] maps to inverse mirror branch",
            "candidate_form": "S_path[gamma,L]=S_path[PT gamma,L^{-1}]",
            "closed": False,
            "blocker": "PT fixed surface/path law is not derived",
        },
        {
            "slot": "boundary_density",
            "requirement": "B_PT is covariant and supplies endpoint terms for variation",
            "candidate_form": "B_PT[gamma endpoints,g_plus,g_minus,L]",
            "closed": False,
            "blocker": "endpoint/surface data are not source-selected",
        },
    ]
    return {
        "description": (
            "Scalar-density completion gate for S_path. Before metric variation can "
            "derive K_plus/K_minus, the path action must be a covariant scalar "
            "density with source-fixed ingredients."
        ),
        "status": "spath-scalar-density-completion-open",
        "depends_on": ["p0_route_c_minimal_spath_extension_axiom_gate"],
        "minimal_spath_status": minimal["status"],
        "completion_rows": completion_rows,
        "scalar_density_contract_written": True,
        "reparametrization_requirement_written": True,
        "diagonal_diffeomorphism_scalar_requirements_written": True,
        "mirror_pt_parity_requirement_written": True,
        "same_l_requirement_preserved": True,
        "scalar_density_source_derived": False,
        "scalar_density_complete": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The covariant scalar-density target is explicit, but every physical "
            "choice that would select C_J, V_J, path measure, Lorentz norm and "
            "boundary data remains source-open."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Route C S_path Scalar-Density Completion Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Scalar density contract written: {payload['scalar_density_contract_written']}",
        f"Reparametrization requirement written: {payload['reparametrization_requirement_written']}",
        (
            "Diagonal diffeomorphism scalar requirements written: "
            f"{payload['diagonal_diffeomorphism_scalar_requirements_written']}"
        ),
        f"Mirror PT parity requirement written: {payload['mirror_pt_parity_requirement_written']}",
        f"Same-L requirement preserved: {payload['same_l_requirement_preserved']}",
        f"Scalar density source-derived: {payload['scalar_density_source_derived']}",
        f"Scalar density complete: {payload['scalar_density_complete']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| slot | requirement | candidate form | closed | blocker |",
        "|---|---|---|---:|---|",
    ]
    for row in payload["completion_rows"]:
        lines.append(
            f"| {row['slot']} | {row['requirement']} | `{row['candidate_form']}` | "
            f"{row['closed']} | {row['blocker']} |"
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
