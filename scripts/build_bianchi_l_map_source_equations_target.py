from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/bianchi_l_map_source_equations_target.md")
JSON_PATH = Path("outputs/reports/bianchi_l_map_source_equations_target.json")


def build_payload() -> dict:
    l_map_definitions = {
        "L_minus_to_plus": (
            "source-derived tangent/tetrad map transporting negative-sector vectors "
            "into the positive-sector frame used by Q_cross and K_plus"
        ),
        "L_plus_to_minus": (
            "source-derived tangent/tetrad map transporting positive-sector vectors "
            "into the negative-sector frame used by Q_cross mirror terms and K_minus"
        ),
        "raw_L_geom": (
            "L_geom=e_plus E_minus is a bookkeeping frame product only; it is not "
            "an admissible optical or Bianchi transport map unless extra conditions hold"
        ),
    }
    admissibility_requirements = [
        "where used optically, require L_minus_to_plus^T eta L_minus_to_plus=eta",
        "where used optically, require L_plus_to_minus^T eta L_plus_to_minus=eta",
        "preserve time orientation on physical four-velocity branches",
        "do not identify raw L_geom with L_minus_to_plus or L_plus_to_minus without a Lorentz proof",
    ]
    differential_transport_equations = [
        "D_alpha L_minus_to_plus^A_B = F_minus_to_plus^A_{B alpha}[g_plus,g_minus,C,T_plus,T_minus]",
        "D_alpha L_plus_to_minus^A_B = F_plus_to_minus^A_{B alpha}[g_minus,g_plus,C,T_minus,T_plus]",
        "u_{-to+}^alpha D_alpha L_minus_to_plus terms must cancel the positive residual force target",
        "u_{+to-}^alpha D_alpha L_plus_to_minus terms must cancel the negative residual force target",
    ]
    induced_transport_requirements = [
        "the same L_minus_to_plus must induce M_minus_to_plus",
        "M_minus_to_plus must define K_plus from transported T_minus",
        "the same L_plus_to_minus must induce M_plus_to_minus",
        "M_plus_to_minus must define K_minus from transported T_plus",
        "Q_cross and K_plus/K_minus cannot use different cross-sector maps",
    ]
    residual_closure_requirements = [
        "insert induced K_plus into R_plus^mu=D_plus_nu(T_plus^{mu nu}+B_plus K_plus^{mu nu})",
        "insert induced K_minus into R_minus^mu=D_minus_nu(B_minus K_minus^{mu nu}+T_minus^{mu nu})",
        "prove R_plus^mu=0 and R_minus^mu=0 after source-derived D L equations are substituted",
    ]
    unresolved_inputs = [
        "derive F_minus_to_plus and F_plus_to_minus from Janus coupled field/source equations",
        "fix whether L acts in tetrad, tangent-coordinate, or mixed index form for each contraction",
        "prove Lorentz admissibility on optical branches, not merely at a single point",
        "prove density-measure compatibility with B_plus/B_minus and Q_det",
        "extend dust branch to perfect fluid and anisotropic stress",
    ]
    forbidden_shortcuts = [
        "do not set D L=0 globally without source equations",
        "do not use raw L_geom=e_plus E_minus as optical L unless L_geom^T eta L_geom=eta is proved",
        "do not choose L from lensing data or sigma8 normalization",
        "do not claim Bianchi closure before both induced residuals vanish",
    ]
    return {
        "description": "P0 target for source-derived cross-sector L maps needed by Bianchi transport and Q_cross.",
        "status": "source-equations-target",
        "source_derived": False,
        "lorentz_admissibility_proved": False,
        "differential_transport_derived": False,
        "induces_bianchi_transport": False,
        "residuals_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "l_map_definitions": l_map_definitions,
        "admissibility_requirements": admissibility_requirements,
        "differential_transport_equations": differential_transport_equations,
        "induced_transport_requirements": induced_transport_requirements,
        "residual_closure_requirements": residual_closure_requirements,
        "unresolved_inputs": unresolved_inputs,
        "forbidden_shortcuts": forbidden_shortcuts,
        "verdict": (
            "This defines the equations the L maps must satisfy. It is not a "
            "Janus derivation yet, and it does not make lensing or simulation predictions."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Bianchi L-Map Source Equations Target",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Source-derived: {payload['source_derived']}",
        f"Lorentz admissibility proved: {payload['lorentz_admissibility_proved']}",
        f"Differential transport derived: {payload['differential_transport_derived']}",
        f"Induces Bianchi transport: {payload['induces_bianchi_transport']}",
        f"Residuals closed: {payload['residuals_closed']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## L-Map Definitions",
        "",
    ]
    lines.extend(f"- `{key}`: {value}" for key, value in payload["l_map_definitions"].items())
    lines.extend(["", "## Admissibility Requirements", ""])
    lines.extend(f"- {item}" for item in payload["admissibility_requirements"])
    lines.extend(["", "## Differential Transport Equations", ""])
    lines.extend(f"- `{item}`" for item in payload["differential_transport_equations"])
    lines.extend(["", "## Induced Transport Requirements", ""])
    lines.extend(f"- {item}" for item in payload["induced_transport_requirements"])
    lines.extend(["", "## Residual Closure Requirements", ""])
    lines.extend(f"- {item}" for item in payload["residual_closure_requirements"])
    lines.extend(["", "## Unresolved Inputs", ""])
    lines.extend(f"- {item}" for item in payload["unresolved_inputs"])
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
