from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_effective_vlasov_transport_target.md")
JSON_PATH = Path("outputs/reports/p0_eft_effective_vlasov_transport_target.json")


def build_payload() -> dict:
    vlasov = {
        "sheet_hamiltonian": "H_s(x,p)=1/2 g_s^{mu nu}(x) p_mu p_nu",
        "liouville_operator": "L_s f_s = dx^mu/dlambda partial_mu f_s + dp_mu/dlambda partial_p_mu f_s",
        "geodesic_flow": "dx^mu/dlambda = partial H_s / partial p_mu; dp_mu/dlambda = -partial H_s / partial x^mu",
        "collisionless_equation": "L_s f_s = 0 on each sheet before bridge coupling",
    }
    bridge_transport = {
        "bridge_map": "Phi: T*Sigma_other -> T*Sigma_self induced by same-L/tetrad soldering",
        "distribution_pullback": "f_other_to_self = f_other o Phi^{-1}",
        "measure_jacobian": "dPi_other_to_self = |det D Phi^{-1}| dPi_self",
        "open_dependency": "exact Phi / same-L bridge still required for a numeric/source-derived Jacobian",
    }
    theorem_status = {
        "vlasov_equation_derived_per_sheet": True,
        "bridge_transport_form_written": True,
        "phase_space_jacobian_defined": True,
        "same_L_bridge_exact": False,
        "phase_space_measure_closed": False,
        "stress_tensor_moments_closed": False,
        "prediction_ready_unconditional": False,
    }
    obligations = [
        "derive the exact same-L bridge Phi from Janus tetrad/pullback geometry",
        "compute |det D Phi| for phase-space measure transport",
        "then compute T^{mu nu} moments and pressure/Pi hierarchy",
    ]
    return {
        "description": "Effective Vlasov transport target for Janus two-sheet matter.",
        "status": "vlasov-per-sheet-derived-bridge-open",
        "vlasov": vlasov,
        "bridge_transport": bridge_transport,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "The collisionless Vlasov equation is derived per sheet. Full matter closure still "
            "requires the exact same-L bridge and its phase-space Jacobian."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Effective Vlasov Transport Target",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## Vlasov",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["vlasov"].items())
    lines.extend(["", "## Bridge Transport"])
    lines.extend(f"- {key}: {value}" for key, value in payload["bridge_transport"].items())
    lines.extend(["", "## Status"])
    lines.extend(f"- {key}: {value}" for key, value in payload["theorem_status"].items())
    lines.extend(["", "## Obligations"])
    lines.extend(f"- {item}" for item in payload["obligations"])
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
