from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/qcross_geometric_tetrad_map_derivation.md")
JSON_PATH = Path("outputs/reports/qcross_geometric_tetrad_map_derivation.json")


def build_payload() -> dict:
    definitions = {
        "coframe": "theta_s^A=e_s^A_mu dx^mu",
        "inverse_frame": "E_s_B^mu e_s^A_mu=delta_B^A",
        "geometric_solder_map": "L_geom_minus_to_plus^A_B=e_plus^A_mu E_minus_B^mu",
        "transported_velocity": "u_minus_to_plus^A=L_geom_minus_to_plus^A_B u_minus^B",
        "projection": "A_minus=(eta_AB u_minus_to_plus^A k_plus^B)^2",
    }
    compatibility = [
        "(L_geom^T eta L_geom)_BC = g_plus_mu_nu E_minus_B^mu E_minus_C^nu",
        "L_geom is Lorentz only if L_geom^T eta L_geom = eta",
        "for g_plus != g_minus, L_geom is a raw solder map, not automatically an admissible Lorentz transport",
    ]
    flrw_diagonal_example = {
        "metric": "ds_s^2=-N_s^2dt^2+a_s^2 gamma_ij dx^i dx^j",
        "l_geom": "diag(N_plus/N_minus, a_plus/a_minus, a_plus/a_minus, a_plus/a_minus)",
        "comoving_projection_ratio": "Q_raw_geom=(N_plus/N_minus)^2",
        "status": "gauge/metric-comparison warning, not final Q_cross",
    }
    next_requirements = [
        "choose or derive a Lorentz-admissible transport from the Janus coupled metrics",
        "separate raw geometric soldering from optical projection amplitude",
        "do not set L_minus_to_plus=L_geom unless L_geom^T eta L_geom=eta is proved",
        "feed only Lorentz-admissible transported velocities into Q_cross",
        "check compatibility with Bianchi K_plus/K_minus transport before tensor claims",
    ]
    return {
        "description": "Geometric tetrad-map derivation for the raw minus-to-plus solder map.",
        "status": "geometric-derivation",
        "algebra_closed": True,
        "physics_closed": False,
        "definitions": definitions,
        "compatibility": compatibility,
        "flrw_diagonal_example": flrw_diagonal_example,
        "next_requirements": next_requirements,
        "verdict": (
            "The raw tetrad solder map is L_geom=e_plus E_minus. It is useful "
            "bookkeeping, but it is not an admissible optical transport unless its "
            "Lorentz compatibility is derived or replaced by a Lorentz map."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Q_cross Geometric Tetrad Map Derivation",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Algebra closed: {payload['algebra_closed']}",
        f"Physics closed: {payload['physics_closed']}",
        "",
        "## Definitions",
        "",
    ]
    for key, value in payload["definitions"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", "## Compatibility", ""])
    lines.extend(f"- `{item}`" for item in payload["compatibility"])
    lines.extend(["", "## FLRW Diagonal Example", ""])
    for key, value in payload["flrw_diagonal_example"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", "## Next Requirements", ""])
    lines.extend(f"- {item}" for item in payload["next_requirements"])
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
