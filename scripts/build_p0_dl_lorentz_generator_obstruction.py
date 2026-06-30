from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_dl_lorentz_generator_obstruction.md")
JSON_PATH = Path("outputs/reports/p0_dl_lorentz_generator_obstruction.json")


def build_payload() -> dict:
    derivation_rows = [
        {
            "claim": "admissible D_alpha L_minus_to_plus = F_alpha L_minus_to_plus",
            "derivation": (
                "D_alpha(L^T eta L)=0 gives "
                "(F_alpha L)^T eta L + L^T eta (F_alpha L)=0, hence "
                "L^T(F_alpha^T eta + eta F_alpha)L=0 and "
                "F_alpha^T eta + eta F_alpha=0"
            ),
            "status": "necessary-not-source-derived",
        },
        {
            "claim": "mirror derivative for L_plus_to_minus",
            "derivation": (
                "if L_plus_to_minus=L_minus_to_plus^{-1}, then "
                "D_alpha L_plus_to_minus = -L_plus_to_minus "
                "(D_alpha L_minus_to_plus) L_plus_to_minus"
            ),
            "status": "mirror-target-not-source-derived",
        },
        {
            "claim": "same L for K and Q_cross",
            "derivation": (
                "K_plus/K_minus transport and optical Q_cross contractions must "
                "use the same L_minus_to_plus and L_plus_to_minus maps"
            ),
            "status": "compatibility-target-open",
        },
    ]
    residual_cancellation_terms = [
        {
            "residual": "R_plus",
            "needed_terms": [
                "D_plus_alpha L_minus_to_plus",
                "F_plus_alpha L_minus_to_plus",
                "connection-difference terms acting on transported minus-sector stress",
                "D_plus_alpha log B_4vol_plus_from_minus measure terms",
            ],
            "closed": False,
        },
        {
            "residual": "R_minus",
            "needed_terms": [
                "D_minus_alpha L_plus_to_minus",
                "mirror F_minus_alpha L_plus_to_minus generator terms",
                "connection-difference terms acting on transported plus-sector stress",
                "D_minus_alpha log B_4vol_minus_from_plus measure terms",
            ],
            "closed": False,
        },
    ]
    missing_source_derived_identities = [
        "source-derived F_alpha for D_alpha L_minus_to_plus = F_alpha L_minus_to_plus",
        "proof that F_alpha^T eta + eta F_alpha = 0 follows from Janus source equations",
        "source-derived L_plus_to_minus derivative or inverse/mirror transport law",
        "same source-derived L maps for K_plus/K_minus and Q_cross",
        "R_plus cancellation including D L, connection-difference, and measure terms",
        "R_minus cancellation including mirror D L, connection-difference, and measure terms",
    ]
    rejection_rules = [
        "do not claim closure from the Lorentz-generator necessary condition alone",
        "do not set D_alpha L=0 unless source equations derive it",
        "do not use one L for K and another L for Q_cross",
        "do not publish a prediction while R_plus or R_minus remains open",
    ]
    return {
        "description": "P0 obstruction artifact for the D L/F_alpha Lorentz-generator blocker.",
        "status": "obstruction-open",
        "lorentz_generator_condition_derived": True,
        "source_derived_generator": False,
        "mirror_derivative_source_derived": False,
        "same_l_for_k_and_qcross_source_derived": False,
        "r_plus_closed": False,
        "r_minus_closed": False,
        "closure_claimed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "derivation_rows": derivation_rows,
        "residual_cancellation_terms": residual_cancellation_terms,
        "missing_source_derived_identities": missing_source_derived_identities,
        "rejection_rules": rejection_rules,
        "verdict": (
            "The Lorentz-generator equation is a necessary admissibility condition, "
            "not a closure proof. Physics and prediction remain false until the "
            "generator, mirror transport, shared K/Q_cross map, and both residual "
            "cancellations are source-derived."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 D L Lorentz-Generator Obstruction",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Lorentz-generator condition derived: {payload['lorentz_generator_condition_derived']}",
        f"Source-derived generator: {payload['source_derived_generator']}",
        f"Mirror derivative source-derived: {payload['mirror_derivative_source_derived']}",
        f"Same L for K and Q_cross source-derived: {payload['same_l_for_k_and_qcross_source_derived']}",
        f"R_plus closed: {payload['r_plus_closed']}",
        f"R_minus closed: {payload['r_minus_closed']}",
        f"Closure claimed: {payload['closure_claimed']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Derivation Rows",
        "",
    ]
    for row in payload["derivation_rows"]:
        lines.append(f"- `{row['claim']}`")
        lines.append(f"  - derivation: `{row['derivation']}`")
        lines.append(f"  - status: {row['status']}")
    lines.extend(["", "## Residual Cancellation Terms", ""])
    for row in payload["residual_cancellation_terms"]:
        terms = "; ".join(f"`{term}`" for term in row["needed_terms"])
        lines.append(f"- {row['residual']}: {terms}")
        lines.append(f"  - closed: {row['closed']}")
    lines.extend(["", "## Missing Source-Derived Identities", ""])
    lines.extend(f"- {item}" for item in payload["missing_source_derived_identities"])
    lines.extend(["", "## Rejection Rules", ""])
    lines.extend(f"- {item}" for item in payload["rejection_rules"])
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
