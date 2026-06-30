from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/lensing_prefactor_audit.md")
JSON_PATH = Path("outputs/reports/lensing_prefactor_audit.json")


ROWS = [
    {
        "item": "C_std",
        "formula": "(3/2) Omega_abs (H0/c)^2 = 4 pi G rho_abs0 / c^2",
        "status": "implemented scaffold",
        "rule": "Allowed only as a standard normalization scaffold.",
    },
    {
        "item": "rho_abs0",
        "formula": "rho_abs0 = rho_+0 + rho_-0_abs",
        "status": "current contrast normalizer",
        "rule": "Not equivalent to an observed Omega_m unless a tracer/selection model is specified.",
    },
    {
        "item": "rho_source",
        "formula": "rho_source = rho_+ - Q_det Q_cross rho_-_abs",
        "status": "source-derived form isolated",
        "rule": "Its mean-subtracted contrast is diagnostic until Q_det and Q_cross conventions are fixed.",
    },
    {
        "item": "Omega_eff",
        "formula": "S8_eff = sigma8_lens_eff sqrt(Omega_eff/0.3)",
        "status": "not admissible",
        "rule": "Cannot be chosen from data; must follow from the physical source normalization and survey observable.",
    },
]


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "description": "Audit of absolute weak-lensing prefactor choices for Janus.",
        "verdict": (
            "Keep Omega_abs as an explicit scaffold input. Do not report Omega_eff or "
            "S8_eff until the tensor source normalization and survey likelihood are fixed."
        ),
        "rows": ROWS,
    }
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")

    lines = [
        "# Lensing Prefactor Audit",
        "",
        payload["description"],
        "",
        "| item | formula | status | rule |",
        "|---|---|---|---|",
    ]
    for row in ROWS:
        lines.append(
            f"| `{row['item']}` | {row['formula']} | {row['status']} | {row['rule']} |"
        )
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
