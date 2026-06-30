from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/interaction_tensor_attempt_audit.md")
JSON_PATH = Path("outputs/reports/interaction_tensor_attempt_audit.json")


def build_payload() -> dict:
    rows = [
        {
            "item": "FLRW interaction scalars",
            "source_equations": "X2025 technical book Eqs. 51-55",
            "working_form": "Phi=a_minus^3/a_plus^3, Phi_bar=Phi^-1, E=rho_plus c^2 a_plus^3 + rho_minus c_minus^2 a_minus^3 = const",
            "status": "roadmap-source",
            "next_required": "verify notation against PDF layout and map signs to M30 mixed equations",
        },
        {
            "item": "determinant reinterpretation",
            "source_equations": "X2025 technical book Eqs. 58-60",
            "working_form": "a_minus^3/a_plus^3 = sqrt(g_minus/g_plus) in FLRW; rewrite sources with determinant-weighted K tensors",
            "status": "roadmap-source",
            "next_required": "derive whether this is proper-density or positive-effective density in optical source",
        },
        {
            "item": "stationary spherical mixed tensors",
            "source_equations": "X2025 technical book Eq. 61 and discussion",
            "working_form": "mixed K tensors with pressure-sign modification and small epsilon",
            "status": "partial-branch",
            "next_required": "derive exact non-perturbative stress tensor, not only second-order Bianchi satisfaction",
        },
        {
            "item": "dipole repeller induced geometry",
            "source_equations": "X2025 technical book Sect. XI",
            "working_form": "positive photons traverse negative conglomerate; induced inner/outer geometry gives annular dimming prediction",
            "status": "observable-target",
            "next_required": "turn spherical negative-mass lens into a ray/brightness-map diagnostic",
        },
        {
            "item": "strong positive-sector objects",
            "source_equations": "X2025 technical book Eqs. 63-64",
            "working_form": "second induced metric needs K with zero-divergence condition",
            "status": "not-closed",
            "next_required": "supply K_mu_nu satisfying the relevant covariant divergence before exact tensor claims",
        },
    ]
    return {
        "description": "Audit of the 2025 Janus technical-book interaction-tensor attempts.",
        "source_id": "X2025-technical-book",
        "source_url": "http://www.jp-petit.org/papers/cosmo/2025-04-25-The-Janus-Cosmological-Model.pdf",
        "source_status": "author technical book / roadmap input, not treated as peer-reviewed proof",
        "rows": rows,
        "verdict": (
            "The 2025 document sharpens the tensor target and gives useful FLRW, "
            "stationary and dipole-repeller branches, but it still does not close "
            "the exact mixed interaction tensor for survey-level lensing."
        ),
    }


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")

    lines = [
        "# Interaction Tensor Attempt Audit",
        "",
        payload["description"],
        "",
        f"Source: `{payload['source_id']}`.",
        f"URL: `{payload['source_url']}`.",
        f"Status: {payload['source_status']}.",
        "",
        "| item | source equations | working form | status | next required |",
        "|---|---|---|---|---|",
    ]
    for row in payload["rows"]:
        lines.append(
            f"| {row['item']} | {row['source_equations']} | {row['working_form']} | "
            f"{row['status']} | {row['next_required']} |"
        )
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
