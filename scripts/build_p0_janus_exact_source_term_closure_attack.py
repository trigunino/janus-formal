from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_janus_exact_source_term_closure_attack.md")
JSON_PATH = Path("outputs/reports/p0_janus_exact_source_term_closure_attack.json")


def build_payload() -> dict:
    closure_axes = [
        {
            "axis": "measure",
            "non_rustine_rule": "B_4vol must be the pulled source volume form divided by the receiver volume form",
            "candidate_formula": "B_4vol = phi^*(sqrt(-g_to)) J_phi / sqrt(-g_self)",
            "closed_by_route": "pullback-volume action",
            "closed": True,
        },
        {
            "axis": "boundary_gauge",
            "non_rustine_rule": "boundary data must be part of the variational problem, not chosen from observations",
            "candidate_formula": "xi|boundary=0 or natural n_a J_phi^a=0; periodic boxes require zero-mean modes",
            "closed_by_route": "variational domain plus mirror inverse constraint",
            "closed": False,
        },
        {
            "axis": "l_sector",
            "non_rustine_rule": "do not pick an independent L; derive it from phi and the two tetrads when possible",
            "candidate_formula": "L_solder = e_self^{-1} dphi e_to, then project/test Lorentz compatibility",
            "closed_by_route": "tetrad-soldered same-L route",
            "closed": False,
        },
        {
            "axis": "e_phi",
            "non_rustine_rule": "E_phi comes from varying the pulled source tensor and B_4vol",
            "candidate_formula": "E_phi[xi] = delta_phi S_cross = integral source * Lie_xi(pulled fields) + boundary",
            "closed_by_route": "source-pullback Euler equation",
            "closed": False,
        },
        {
            "axis": "e_l",
            "non_rustine_rule": "E_L is either a Lorentz torque constraint or disappears if L is soldered from phi",
            "candidate_formula": "E_L[Lambda]=antisym_AB((L^T P)_AB)=0",
            "closed_by_route": "same-L tensor pairing, then residual rotation gauge",
            "closed": False,
        },
    ]
    route_tests = [
        {
            "route": "pure_pullback_volume",
            "fixes_measure": True,
            "fixes_boundary_gauge": False,
            "fixes_l": False,
            "verdict": "necessary but insufficient",
        },
        {
            "route": "independent_l_lorentz_variation",
            "fixes_measure": False,
            "fixes_boundary_gauge": False,
            "fixes_l": False,
            "verdict": "only gives antisymmetric torque; symmetric dust leaves gauge freedom",
        },
        {
            "route": "tetrad_soldered_same_l",
            "fixes_measure": True,
            "fixes_boundary_gauge": False,
            "fixes_l": True,
            "verdict": "best no-rustine route to test next",
        },
        {
            "route": "gl_strain_action",
            "fixes_measure": False,
            "fixes_boundary_gauge": False,
            "fixes_l": True,
            "verdict": "possible only with new stability/source proof",
        },
    ]
    next_derivations = [
        "use p0_janus_soldered_l_substitution_residual_gate for L_solder and K/Q_cross/Vlasov substitution",
        "use p0_janus_metric_pullback_compatibility_gate for the Lorentz iff metric-pullback theorem",
        "vary B_4vol under xi and integrate by parts with explicit boundary choice",
        "prove mirror inverse maps the plus equation to the minus equation",
        "if Lorentz compatibility fails, prove a no-go for pure tetrad-soldered closure",
    ]
    return {
        "description": "Attack plan for closing the exact Janus source term without fit or arbitrary patch.",
        "status": "best-route-selected-tetrad-soldered-same-l-open",
        "closure_axes": closure_axes,
        "route_tests": route_tests,
        "next_derivations": next_derivations,
        "measure_candidate_fixed": True,
        "boundary_gauge_candidate_fixed": False,
        "l_candidate_route_selected": True,
        "l_candidate_route": "tetrad_soldered_same_l",
        "soldered_l_substitution_artifact": "p0_janus_soldered_l_substitution_residual_gate",
        "soldered_l_derivation_available": True,
        "metric_pullback_compatibility_artifact": "p0_janus_metric_pullback_compatibility_gate",
        "metric_pullback_compatibility_derived": True,
        "e_phi_candidate_source": "pullback-volume source variation",
        "e_l_candidate_source": "Lorentz torque or soldered-L compatibility residual",
        "requires_observational_fit": False,
        "introduces_new_axiom": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The next expert move is not to invent a free S_couple. Use the pulled volume "
            "to fix B_4vol, derive L from phi and tetrads as the same-L soldering map, "
            "then test the remaining boundary/gauge and Lorentz-compatibility residuals."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Exact Source Term Closure Attack",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Measure candidate fixed: {payload['measure_candidate_fixed']}",
        f"Boundary/gauge candidate fixed: {payload['boundary_gauge_candidate_fixed']}",
        f"L candidate route selected: {payload['l_candidate_route_selected']}",
        f"L candidate route: `{payload['l_candidate_route']}`",
        f"Soldered-L substitution artifact: `{payload['soldered_l_substitution_artifact']}`",
        f"Soldered-L derivation available: {payload['soldered_l_derivation_available']}",
        "Metric pullback compatibility artifact: "
        f"`{payload['metric_pullback_compatibility_artifact']}`",
        f"Metric pullback compatibility derived: {payload['metric_pullback_compatibility_derived']}",
        f"E_phi candidate source: {payload['e_phi_candidate_source']}",
        f"E_L candidate source: {payload['e_l_candidate_source']}",
        f"Requires observational fit: {payload['requires_observational_fit']}",
        f"Introduces new axiom: {payload['introduces_new_axiom']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Closure Axes",
        "",
        "| axis | rule | candidate formula | route | closed |",
        "|---|---|---|---|---:|",
    ]
    for row in payload["closure_axes"]:
        lines.append(
            f"| {row['axis']} | {row['non_rustine_rule']} | `{row['candidate_formula']}` | "
            f"{row['closed_by_route']} | {row['closed']} |"
        )
    lines.extend(
        [
            "",
            "## Route Tests",
            "",
            "| route | measure | boundary/gauge | L | verdict |",
            "|---|---:|---:|---:|---|",
        ]
    )
    for row in payload["route_tests"]:
        lines.append(
            f"| {row['route']} | {row['fixes_measure']} | {row['fixes_boundary_gauge']} | "
            f"{row['fixes_l']} | {row['verdict']} |"
        )
    lines.extend(["", "## Next Derivations", ""])
    lines.extend(f"- {item}" for item in payload["next_derivations"])
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
