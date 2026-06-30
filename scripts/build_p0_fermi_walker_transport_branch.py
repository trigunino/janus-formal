from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_fermi_walker_transport_branch.md")
JSON_PATH = Path("outputs/reports/p0_fermi_walker_transport_branch.json")


def build_payload() -> dict:
    branch_definition = [
        "Omega_alpha=(D_alpha L)L^{-1}, Omega_{alpha AB}=-Omega_{alpha BA}",
        "Along transported flow u: Omega_u^{AB}=u^A a^B-a^A u^B",
        "a^A=u^B D_receiver_B u^A is the receiver-frame acceleration",
        "Minimal rotation condition: projected rest-space rotation P Omega_u P = 0",
    ]
    plus_branch = {
        "transported_flow": "u_-to+=L_minus_to_plus u_-",
        "receiver_force_target": "a_-to+^A=u_-to+^B D_plus_B u_-to+^A=0",
        "fermi_walker_result": "Omega_{u,-to+}^{AB}=0 along dust receiver-geodesic flow",
        "closes_force_if": "transported negative flow is D_plus-geodesic and density terms close",
    }
    minus_branch = {
        "transported_flow": "u_+to-=L_plus_to_minus u_+",
        "receiver_force_target": "a_+to-^A=u_+to-^B D_minus_B u_+to-^A=0",
        "fermi_walker_result": "Omega_{u,+to-}^{AB}=0 along dust receiver-geodesic flow",
        "closes_force_if": "transported positive flow is D_minus-geodesic and density terms close",
    }
    qcross_effect = [
        "minimal rotation preserves the local boost-derived Q_cross for a fixed transported u and photon direction",
        "screen-frame rotations are set to zero along u, so they cannot be used as hidden lensing amplitudes",
        "Q_cross still changes if the source-derived relative velocity/boost changes",
    ]
    what_it_fixes = [
        "removes arbitrary rest-space rotation along the transported dust flow",
        "selects a unique no-twist frame along each dust worldline once u and acceleration are known",
        "keeps Lorentz admissibility because Omega is eta-antisymmetric",
    ]
    what_it_does_not_fix = [
        "does not derive the transported receiver-geodesic equation itself",
        "does not fix transverse variation of L away from the dust flow",
        "does not fix B_plus/B_minus density-measure gradients",
        "does not transport pressure or anisotropic stress",
        "does not become Janus-source-derived without an action/geometric principle selecting Fermi-Walker transport",
    ]
    acceptance_tests = [
        "prove Janus equations imply receiver-geodesic transported flows",
        "prove minimal-rotation gauge follows from symmetry/action, not convention",
        "verify R_plus=0 and R_minus=0 including B gradients",
        "verify same L gives K_plus/K_minus and Q_cross",
    ]
    return {
        "description": "Candidate Fermi-Walker minimal-rotation branch for the residual F=D L freedom.",
        "status": "candidate-gauge-branch",
        "lorentz_preserving": True,
        "minimal_rotation_written": True,
        "dust_force_closed_conditionally": True,
        "source_derived": False,
        "transverse_variation_fixed": False,
        "pressure_pi_fixed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "branch_definition": branch_definition,
        "plus_branch": plus_branch,
        "minus_branch": minus_branch,
        "qcross_effect": qcross_effect,
        "what_it_fixes": what_it_fixes,
        "what_it_does_not_fix": what_it_does_not_fix,
        "acceptance_tests": acceptance_tests,
        "verdict": (
            "Fermi-Walker minimal rotation is the cleanest dust gauge candidate: it "
            "removes arbitrary rest-space rotation without fitting Q_cross. It is not "
            "a physical Janus closure until source equations select it and both "
            "Bianchi residuals close with density terms."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Fermi-Walker Transport Branch",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Lorentz preserving: {payload['lorentz_preserving']}",
        f"Minimal rotation written: {payload['minimal_rotation_written']}",
        f"Dust force closed conditionally: {payload['dust_force_closed_conditionally']}",
        f"Source-derived: {payload['source_derived']}",
        f"Transverse variation fixed: {payload['transverse_variation_fixed']}",
        f"Pressure/Pi fixed: {payload['pressure_pi_fixed']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Branch Definition",
        "",
    ]
    lines.extend(f"- `{item}`" for item in payload["branch_definition"])
    lines.extend(["", "## Plus Branch", ""])
    lines.extend(f"- {key}: `{value}`" for key, value in payload["plus_branch"].items())
    lines.extend(["", "## Minus Branch", ""])
    lines.extend(f"- {key}: `{value}`" for key, value in payload["minus_branch"].items())
    lines.extend(["", "## Q_cross Effect", ""])
    lines.extend(f"- {item}" for item in payload["qcross_effect"])
    lines.extend(["", "## What It Fixes", ""])
    lines.extend(f"- {item}" for item in payload["what_it_fixes"])
    lines.extend(["", "## What It Does Not Fix", ""])
    lines.extend(f"- {item}" for item in payload["what_it_does_not_fix"])
    lines.extend(["", "## Acceptance Tests", ""])
    lines.extend(f"- {item}" for item in payload["acceptance_tests"])
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
