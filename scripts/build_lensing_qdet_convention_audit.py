from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/lensing_qdet_convention_audit.md")
JSON_PATH = Path("outputs/reports/lensing_qdet_convention_audit.json")


CONVENTIONS = [
    {
        "name": "raw_metric_ratio",
        "definition": "B = sqrt((-g_-)/(-g_+)) = (a_-/a_+)^4, source rho_+ - B Q_cross rho_-",
        "source_anchor": "M15 determinant roots; FLRW ansatz",
        "code_surface": "negative_sector_lensing_weight_factor(negative_density_convention='negative_proper', ...)",
        "status": "algebraic only",
        "admissible_now": False,
        "reason": "Needs proof that input rho_- is a negative-sector proper density in the same coordinate volume.",
    },
    {
        "name": "m20_scale_ratio_inserted",
        "definition": "B = (1/100)^4 from M20 a_-/a_+ ~= 1/100",
        "source_anchor": "M20 Eq. 10",
        "code_surface": "none",
        "status": "forbidden shortcut",
        "admissible_now": False,
        "reason": "M20 scale ratio is a CMB-imprint scale argument, not a verified optical determinant amplitude.",
    },
    {
        "name": "newtonian_effective_density",
        "definition": "B ~= 1, with rho_- interpreted as the effective density entering the positive Newtonian limit; source rho_+ - Q_cross rho_-",
        "source_anchor": "M30 Eq. 124 and M15/M30 Newtonian sign reduction",
        "code_surface": "negative_sector_lensing_weight_factor(negative_density_convention='positive_effective', ...)",
        "status": "current weak-field convention",
        "admissible_now": True,
        "reason": "This is the convention already used by the signed Poisson/lensing diagnostic, not a final tensor normalization.",
    },
    {
        "name": "perturbative_metric_ratio",
        "definition": "B = 1 + (epsilon/2) * (tr_- - tr_+) + O(epsilon^2), source rho_+ - B Q_cross rho_-",
        "source_anchor": "M15 determinant roots plus local symbolic expansion",
        "code_surface": "negative_sector_lensing_weight_factor(negative_density_convention='negative_proper', ...)",
        "status": "derivation path",
        "admissible_now": False,
        "reason": "Requires the positive and negative metric perturbation traces along the optical path.",
    },
]


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "description": "Convention audit for the Janus lensing determinant factor Q_det.",
        "verdict": (
            "Use B=1 only as the current Newtonian effective-density convention. "
            "Do not insert M20 (a_-/a_+)^4 into lensing until the optical volume "
            "and density convention is derived."
        ),
        "conventions": CONVENTIONS,
    }
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")

    lines = [
        "# Lensing Q_det Convention Audit",
        "",
        payload["description"],
        "",
        "| convention | definition | source anchor | code surface | status | admissible now | reason |",
        "|---|---|---|---|---|---|---|",
    ]
    for row in CONVENTIONS:
        lines.append(
            f"| `{row['name']}` | {row['definition']} | {row['source_anchor']} | "
            f"`{row['code_surface']}` | {row['status']} | {row['admissible_now']} | "
            f"{row['reason']} |"
        )
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
