from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/lensing_qdet_qcross_derivation_map.md")
JSON_PATH = Path("outputs/reports/lensing_qdet_qcross_derivation_map.json")


BRANCHES = [
    {
        "branch": "effective_newtonian",
        "source": "rho_-^eff = Q_det rho_-^proper; rho_source = rho_+ - rho_-^eff",
        "q_det": "1",
        "q_cross": "1",
        "w_minus": "1",
        "status": "admissible diagnostic; Q_det absorbed by rho_-^eff",
        "requirements": "M30 Newtonian determinant-ratio ~=1; equal-projection convention; no final S8_eff.",
    },
    {
        "branch": "effective_with_projection",
        "source": "rho_source = rho_+ - Q_cross rho_-^eff",
        "q_det": "1",
        "q_cross": "(eta_AB u_minus_to_plus^A k_plus^B)^2/(eta_AB u_plus^A k_plus^B)^2",
        "w_minus": "Q_cross",
        "status": "derivation target",
        "requirements": "derive L_minus_to_plus tetrad/covector map along positive photon paths and prove Bianchi K_plus/K_minus compatibility.",
    },
    {
        "branch": "proper_density_full",
        "source": "rho_source = rho_+ - Q_det Q_cross rho_-^proper",
        "q_det": "sqrt(-g_-/-g_+)",
        "q_cross": "(eta_AB u_minus_to_plus^A k_plus^B)^2/(eta_AB u_plus^A k_plus^B)^2",
        "w_minus": "Q_det Q_cross",
        "status": "derivation target",
        "requirements": "derive coordinate volume, proper-density mapping, L_minus_to_plus projection and Bianchi K_plus/K_minus compatibility.",
    },
    {
        "branch": "raw_m20_scale_insert",
        "source": "rho_source = rho_+ - (1/100)^n rho_-",
        "q_det": "(1/100)^4",
        "q_cross": "(1/100)^2",
        "w_minus": "(1/100)^6 if stacked",
        "status": "forbidden",
        "requirements": "not admissible without a gauge/volume derivation; not a fit parameter.",
    },
]


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "description": "Derivation branch map for Janus Q_det and Q_cross in positive-sector lensing.",
        "verdict": (
            "The only admissible current numerical branch is effective_newtonian as a diagnostic. "
            "Final lensing requires either effective_with_projection or proper_density_full to be derived."
        ),
        "branches": BRANCHES,
    }
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")

    lines = [
        "# Lensing Q_det/Q_cross Derivation Map",
        "",
        payload["description"],
        "",
        "| branch | source | Q_det | Q_cross | W_- | status | requirements |",
        "|---|---|---|---|---|---|---|",
    ]
    for row in BRANCHES:
        lines.append(
            f"| `{row['branch']}` | {row['source']} | {row['q_det']} | {row['q_cross']} | "
            f"{row['w_minus']} | {row['status']} | {row['requirements']} |"
        )
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
