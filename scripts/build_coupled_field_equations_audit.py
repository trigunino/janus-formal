from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/coupled_field_equations_audit.md")
JSON_PATH = Path("outputs/reports/coupled_field_equations_audit.json")


def build_payload() -> dict:
    equations = [
        {
            "item": "two metrics",
            "working_form": "g_plus for positive geodesics; g_minus for negative geodesics",
            "status": "accepted-working",
            "next_required": "keep both geodesic families explicit in optical derivations",
        },
        {
            "item": "coupled source signs",
            "working_form": "positive sheet sees rho_plus - weighted rho_minus; negative sheet sees rho_minus - weighted rho_plus",
            "status": "implemented weak-field",
            "next_required": "derive full tensor stress mapping, not only Newtonian sign matrix",
        },
        {
            "item": "determinant ratio",
            "working_form": "B_plus=sqrt(-g_minus/-g_plus), B_minus=sqrt(-g_plus/-g_minus)",
            "status": "working-derivation",
            "next_required": "derive which density convention is used in optical source",
        },
        {
            "item": "stationary symmetric limit",
            "working_form": "B_plus=B_minus=1 gives the anti-Newtonian sign matrix",
            "status": "symbolically checked",
            "next_required": "do not generalize this limit to instationary asymmetric fields",
        },
        {
            "item": "Bianchi closure",
            "working_form": "nabla_plus.G_plus=0 and nabla_minus.G_minus=0 require conserved coupled RHS",
            "status": "open tensor constraint",
            "next_required": "derive mixed stress tensors and determinant terms satisfying each covariant divergence",
        },
    ]
    return {
        "description": "Audit of the coupled-field-equation layer used by Janus PM/lensing diagnostics.",
        "didactic_source": "https://www.januscosmologicalmodel.fr/post/un-syst%C3%A8me-d-%C3%A9quations-de-champs-couple%C3%A9s",
        "source_status": "didactic web page; useful orientation, not a peer-reviewed proof source",
        "equations": equations,
        "verdict": (
            "The weak-field sign structure is implemented, but the full tensor replacement "
            "requires determinant-density mapping plus Bianchi-compatible mixed stress tensors."
        ),
    }


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Coupled Field Equations Audit",
        "",
        payload["description"],
        "",
        f"Didactic source: `{payload['didactic_source']}`.",
        f"Source status: {payload['source_status']}.",
        "",
        "| item | working form | status | next required |",
        "|---|---|---|---|",
    ]
    for row in payload["equations"]:
        lines.append(
            f"| {row['item']} | {row['working_form']} | {row['status']} | "
            f"{row['next_required']} |"
        )
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
