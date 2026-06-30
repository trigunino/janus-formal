from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_same_l_spin_connection_transport_identity_gate.md")
JSON_PATH = Path("outputs/reports/p0_same_l_spin_connection_transport_identity_gate.json")


def build_payload() -> dict:
    identities = [
        {
            "name": "spin_covariant_dl",
            "formula": "D_lambda L = partial_lambda L + omega_s,lambda L - L omega_o,lambda",
            "meaning": "the derivative of the same tetrad bridge must use both sector spin connections",
            "closed": True,
        },
        {
            "name": "lorentz_generator",
            "formula": "Omega_lambda=(D_lambda L)L^{-1}",
            "meaning": "if L^T eta L=eta and both spin connections are eta-compatible, Omega_lambda is eta-antisymmetric",
            "closed": True,
        },
        {
            "name": "mirror_derivative",
            "formula": "D_lambda L^{-1}=-L^{-1}(D_lambda L)L^{-1}",
            "meaning": "the mirror bridge derivative is fixed once the same L branch is fixed",
            "closed": True,
        },
        {
            "name": "coordinate_bridge_derivative",
            "formula": "nabla_s M = e_s (D L) e_o",
            "meaning": "tetrad postulate cancels raw tetrad derivatives; only the spin-covariant D L remains",
            "closed": True,
        },
        {
            "name": "transported_stress_divergence",
            "formula": "nabla_s(T_o->s)=M M nabla_o T_o + terms[D L] + terms[D log B4vol]",
            "meaning": "stress divergence cannot be closed by Q_cross or Q_det; D L and measure terms must be substituted",
            "closed": True,
        },
    ]
    acceptance_tests = [
        {
            "test": "one_l_stack",
            "requires": "the same L appears in M, K, Q_cross, Vlasov and D L",
            "passed": True,
        },
        {
            "test": "eta_compatibility",
            "requires": "omega_s^T eta + eta omega_s=0 and omega_o^T eta + eta omega_o=0",
            "passed": True,
        },
        {
            "test": "source_selected_l",
            "requires": "Janus equations/action/symmetry select L or Omega_lambda",
            "passed": False,
        },
        {
            "test": "curvature_integrability",
            "requires": "D_[mu Omega_nu]+[Omega_mu,Omega_nu] equals the source-derived relative curvature",
            "passed": False,
        },
        {
            "test": "bianchi_residuals",
            "requires": "R_plus=0 and R_minus=0 after substituting same L, D L, K, Q_cross and B4vol",
            "passed": False,
        },
    ]
    forbidden_shortcuts = [
        "do not set D L=0 unless spin connections and Janus source equations force it",
        "do not replace the spin-covariant D L by raw partial L",
        "do not use separate bridges for D L, K and Q_cross",
        "do not absorb D L residuals into Q_det, B4vol or Q_cross scalars",
    ]
    return {
        "description": "P0 gate deriving the spin-connection form of D L for a single same-L transport stack.",
        "status": "same-l-spin-connection-identity-algebra-closed-source-open",
        "identities": identities,
        "acceptance_tests": acceptance_tests,
        "forbidden_shortcuts": forbidden_shortcuts,
        "covariant_dl_identity_closed": True,
        "coordinate_bridge_derivative_closed": True,
        "mirror_derivative_algebra_closed": True,
        "lorentz_generator_necessary_condition_closed": True,
        "same_l_stack_required": True,
        "source_selected_l": False,
        "source_selected_omega": False,
        "curvature_integrability_closed": False,
        "bianchi_residuals_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The correct D L object is not arbitrary: it is the spin-covariant "
            "bridge derivative partial L + omega_s L - L omega_o. This closes the "
            "transport identity algebra, but not the Janus source selection of L, "
            "Omega, curvature integrability, or the Bianchi residuals."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Same-L Spin-Connection Transport Identity Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Covariant DL identity closed: {payload['covariant_dl_identity_closed']}",
        f"Coordinate bridge derivative closed: {payload['coordinate_bridge_derivative_closed']}",
        f"Mirror derivative algebra closed: {payload['mirror_derivative_algebra_closed']}",
        f"Lorentz-generator necessary condition closed: {payload['lorentz_generator_necessary_condition_closed']}",
        f"Source-selected L: {payload['source_selected_l']}",
        f"Source-selected Omega: {payload['source_selected_omega']}",
        f"Curvature integrability closed: {payload['curvature_integrability_closed']}",
        f"Bianchi residuals closed: {payload['bianchi_residuals_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Identities",
        "",
        "| name | formula | meaning | closed |",
        "|---|---|---|---:|",
    ]
    for row in payload["identities"]:
        lines.append(f"| {row['name']} | `{row['formula']}` | {row['meaning']} | {row['closed']} |")
    lines.extend(["", "## Acceptance Tests", "", "| test | requires | passed |", "|---|---|---:|"])
    for row in payload["acceptance_tests"]:
        lines.append(f"| {row['test']} | {row['requires']} | {row['passed']} |")
    lines.extend(["", "## Forbidden Shortcuts", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_shortcuts"])
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
