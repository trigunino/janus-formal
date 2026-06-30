from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/bianchi_lorentz_boost_transport_branch.md")
JSON_PATH = Path("outputs/reports/bianchi_lorentz_boost_transport_branch.json")


def build_payload() -> dict:
    setup = [
        "tetrad metric eta_AB=diag(-1,1,1,1)",
        "negative dust stress T_minus^{AB}=rho_minus u_minus^A u_minus^B",
        "positive dust stress T_plus^{AB}=rho_plus u_plus^A u_plus^B",
        "admissible cross map L_minus_to_plus with L^T eta L=eta",
        "mirror admissible cross map L_plus_to_minus with L^T eta L=eta",
    ]
    algebraic_transport = [
        "u_{-to+}^A = L_minus_to_plus^A_B u_minus^B",
        "K_plus^{AB}=rho_minus u_{-to+}^A u_{-to+}^B",
        "u_{+to-}^A = L_plus_to_minus^A_B u_plus^B",
        "K_minus^{AB}=rho_plus u_{+to-}^A u_{+to-}^B",
    ]
    optical_contractions = [
        "K_plus_kk=rho_minus (k_plus.u_{-to+})^2",
        "K_minus_kk=rho_plus (k_minus.u_{+to-})^2",
        "Q_cross can be read only from these contractions after the same L maps are used by Bianchi transport",
    ]
    divergence_blockers = [
        "R_plus^mu = D_plus_nu S_plus^{mu nu} = 0 is not closed here",
        "R_minus^mu = D_minus_nu S_minus^{mu nu} = 0 is not closed here",
        "source-derived L transport, density transport and connection-divergence terms are still required",
        "algebraic Lorentz admissibility does not imply covariant divergence closure",
    ]
    forbidden_shortcuts = [
        "coordinate volume shortcuts as optical amplitudes",
        "independent optical Q_cross not induced by the same L_minus_to_plus/L_plus_to_minus maps",
        "prediction or tensor-lensing claims before both residuals vanish",
    ]
    return {
        "description": "Bounded Lorentz-boost branch for Bianchi-compatible dust stress transport.",
        "status": "bounded-derivation-branch",
        "algebraic_transport_closed": True,
        "divergence_closure_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "setup": setup,
        "algebraic_transport": algebraic_transport,
        "optical_contractions": optical_contractions,
        "divergence_blockers": divergence_blockers,
        "forbidden_shortcuts": forbidden_shortcuts,
        "verdict": (
            "This closes only the local algebraic Lorentz transport of dust stress. "
            "It does not close R_plus=0 or R_minus=0, so prediction claims remain blocked."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Bianchi Lorentz Boost Transport Branch",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Algebraic transport closed: {payload['algebraic_transport_closed']}",
        f"Divergence closure closed: {payload['divergence_closure_closed']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Setup",
        "",
    ]
    lines.extend(f"- `{item}`" for item in payload["setup"])
    lines.extend(["", "## Algebraic Transport", ""])
    lines.extend(f"- `{item}`" for item in payload["algebraic_transport"])
    lines.extend(["", "## Optical Contractions", ""])
    lines.extend(f"- `{item}`" for item in payload["optical_contractions"])
    lines.extend(["", "## Divergence Blockers", ""])
    lines.extend(f"- `{item}`" for item in payload["divergence_blockers"])
    lines.extend(["", "## Forbidden Shortcuts", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_shortcuts"])
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    return "\n".join(lines)


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(render_markdown(payload), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
