from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_source_measure_convention_matrix.md")
JSON_PATH = Path("outputs/reports/p0_source_measure_convention_matrix.json")


def build_payload() -> dict:
    explicit_measures = [
        {
            "symbol": "B_4vol_plus_from_minus",
            "definition": "sqrt(-g_minus)/sqrt(-g_plus)",
            "contains_lapse": True,
            "use": "field-equation determinant weight",
        },
        {
            "symbol": "V3_dust_plus_from_minus",
            "definition": "sqrt(h_minus)/sqrt(h_plus)",
            "contains_lapse": False,
            "use": "spatial dust-volume bookkeeping on a chosen slice",
        },
        {
            "symbol": "rho_eff_plus_from_minus",
            "definition": "B_4vol_plus_from_minus rho_minus or V3_dust_plus_from_minus rho_minus, but not both",
            "contains_lapse": "depends on selected convention",
            "use": "diagnostic effective source variable",
        },
    ]
    convention_candidates = [
        {
            "name": "field_equation_4volume_source",
            "transported_source": "B_4vol_plus_from_minus T_minus_to_plus^{mu nu}",
            "required_closure": "Bianchi residual must keep D log B_4vol terms or prove cancellation",
            "admissible_for_prediction": False,
        },
        {
            "name": "slice_dust_flux_source",
            "transported_source": "V3_dust_plus_from_minus rho_minus u_minus_to_plus^mu u_minus_to_plus^nu",
            "required_closure": "must be lifted back to the tensor field equation without losing lapse terms",
            "admissible_for_prediction": False,
        },
        {
            "name": "effective_density_source",
            "transported_source": "rho_eff_plus_from_minus u_minus_to_plus^mu u_minus_to_plus^nu",
            "required_closure": "must declare whether rho_eff already absorbed B_4vol or V3_dust",
            "admissible_for_prediction": False,
        },
    ]
    invariants = [
        "exactly one density measure convention is active per derivation branch",
        "Q_det may record metric-volume transport but must not be reapplied to rho_eff",
        "Q_cross remains optical/tetrad projection and never replaces a source measure",
        "lapse-containing B_4vol and slice V3_dust use distinct names in reports and code",
    ]
    rejection_tests = [
        "reject branches multiplying rho_eff by Q_det again",
        "reject branches replacing B_4vol with V3_dust without a lapse/slicing proof",
        "reject scalar absorption of pressure or Pi terms into the density measure",
        "reject any prediction branch while all candidates remain admissible_for_prediction=false",
    ]
    return {
        "description": "P0 source-measure convention matrix separating 4D determinant, 3D dust volume, and effective density.",
        "status": "source-measure-convention-open",
        "explicit_measure_names_fixed": True,
        "single_active_convention_required": True,
        "accepted_convention": None,
        "source_convention_fixed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "explicit_measures": explicit_measures,
        "convention_candidates": convention_candidates,
        "invariants": invariants,
        "rejection_tests": rejection_tests,
        "verdict": (
            "This removes the notation ambiguity, but does not select a physical source convention. "
            "Selection still requires Janus-source traceability and Bianchi residual closure."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Source-Measure Convention Matrix",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Explicit measure names fixed: {payload['explicit_measure_names_fixed']}",
        f"Single active convention required: {payload['single_active_convention_required']}",
        f"Accepted convention: {payload['accepted_convention']}",
        f"Source convention fixed: {payload['source_convention_fixed']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Explicit Measures",
        "",
    ]
    for row in payload["explicit_measures"]:
        lines.append(
            f"- `{row['symbol']}` = `{row['definition']}`; contains_lapse={row['contains_lapse']}; use={row['use']}"
        )
    lines.extend(["", "## Convention Candidates", ""])
    for row in payload["convention_candidates"]:
        lines.append(f"- {row['name']}:")
        lines.append(f"  - transported source: `{row['transported_source']}`")
        lines.append(f"  - required closure: {row['required_closure']}")
        lines.append(f"  - admissible for prediction: {row['admissible_for_prediction']}")
    lines.extend(["", "## Invariants", ""])
    lines.extend(f"- {item}" for item in payload["invariants"])
    lines.extend(["", "## Rejection Tests", ""])
    lines.extend(f"- {item}" for item in payload["rejection_tests"])
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
