from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/bianchi_transported_continuity_target.md")
JSON_PATH = Path("outputs/reports/bianchi_transported_continuity_target.json")


def build_payload() -> dict:
    target_equations = [
        "D_minus_nu(rho_minus u_-to+^nu)=0",
        "D_plus_nu(rho_plus u_+to-^nu)=0",
    ]
    product_rule_expansion = [
        "D_minus_nu(rho_minus u_-to+^nu) = u_-to+^nu D_minus_nu rho_minus + rho_minus D_minus_nu u_-to+^nu",
        "D_plus_nu(rho_plus u_+to-^nu) = u_+to-^nu D_plus_nu rho_plus + rho_plus D_plus_nu u_+to-^nu",
    ]
    dependencies = [
        "density measure used for rho_minus/rho_plus",
        "Q_det convention linking proper density and plus/minus coordinate volume",
        "L_minus_to_plus and L_plus_to_minus maps used to define transported velocities",
        "volume convention for the transported flux, including lapse/slice choice",
    ]
    insufficiency_statement = (
        "Same-sector continuity is insufficient unless the transported L map and "
        "density-volume convention preserve the flux whose divergence is evaluated "
        "in the opposite-sector residual."
    )
    open_proof_obligations = [
        "derive the transported continuity equations from Janus coupled source equations",
        "prove the L maps preserve the relevant particle/energy flux measure",
        "fix whether Q_det uses 4-volume or dust 3-volume for this continuity target",
        "verify compatibility with K_plus/K_minus and Q_cross definitions",
    ]
    forbidden_shortcuts = [
        "do not replace transported continuity with same-sector continuity by notation",
        "do not use raw determinant or scale-factor ratios as lensing amplitudes",
        "do not assume a volume convention before Q_det is source-derived",
        "do not mark Bianchi residuals closed from this target alone",
    ]
    return {
        "description": "Transported continuity target required by Lorentz dust Bianchi closure.",
        "status": "target-open",
        "target_equations_written": True,
        "product_rule_expanded": True,
        "depends_on_qdet_density_measure": True,
        "requires_l_map": True,
        "requires_volume_convention": True,
        "same_sector_continuity_sufficient": False,
        "source_derived": False,
        "residuals_closed": False,
        "prediction_ready": False,
        "target_equations": target_equations,
        "product_rule_expansion": product_rule_expansion,
        "dependencies": dependencies,
        "insufficiency_statement": insufficiency_statement,
        "open_proof_obligations": open_proof_obligations,
        "forbidden_shortcuts": forbidden_shortcuts,
        "verdict": (
            "The needed transported continuity equations are identified and expanded, "
            "but remain open until the L map, Q_det density measure, and volume "
            "convention are derived from Janus equations."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Bianchi Transported Continuity Target",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Target equations written: {payload['target_equations_written']}",
        f"Product rule expanded: {payload['product_rule_expanded']}",
        f"Depends on Q_det density measure: {payload['depends_on_qdet_density_measure']}",
        f"Requires L map: {payload['requires_l_map']}",
        f"Requires volume convention: {payload['requires_volume_convention']}",
        f"Same-sector continuity sufficient: {payload['same_sector_continuity_sufficient']}",
        f"Source-derived: {payload['source_derived']}",
        f"Residuals closed: {payload['residuals_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Target Equations",
        "",
    ]
    lines.extend(f"- `{item}`" for item in payload["target_equations"])
    lines.extend(["", "## Product-Rule Expansion", ""])
    lines.extend(f"- `{item}`" for item in payload["product_rule_expansion"])
    lines.extend(["", "## Dependencies", ""])
    lines.extend(f"- {item}" for item in payload["dependencies"])
    lines.extend(["", "## Insufficiency Statement", ""])
    lines.append(payload["insufficiency_statement"])
    lines.extend(["", "## Open Proof Obligations", ""])
    lines.extend(f"- {item}" for item in payload["open_proof_obligations"])
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
