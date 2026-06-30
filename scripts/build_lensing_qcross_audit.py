from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/lensing_qcross_audit.md")
JSON_PATH = Path("outputs/reports/lensing_qcross_audit.json")


ROWS = [
    {
        "name": "equal_projection_limit",
        "formula": "Q_cross = 1",
        "status": "current weak-field convention",
        "admissible_now": True,
        "rule": "Use only as an explicit equal-comoving/equal-projection assumption.",
    },
    {
        "name": "raw_flrw_lapse_projection",
        "formula": "Q_cross = (a_-/a_+)^2 for coordinate-rest fluids with covariant u_s,k projection",
        "status": "algebraic path only",
        "admissible_now": False,
        "rule": "Do not combine with M20 scale ratio until metric-volume and time-gauge conventions are derived.",
    },
    {
        "name": "raw_flrw_weight_stack",
        "formula": "Q_det Q_cross = (a_-/a_+)^6 if raw FLRW determinant and lapse factors are multiplied",
        "status": "forbidden shortcut",
        "admissible_now": False,
        "rule": "This stacked factor is a warning, not a prediction.",
    },
    {
        "name": "tetrad_covector_map",
        "formula": "Q_cross=(eta_AB u_minus_to_plus^A k_plus^B)^2/(eta_AB u_plus^A k_plus^B)^2",
        "status": "covariant target",
        "admissible_now": False,
        "rule": "Requires a source-derived L_minus_to_plus tetrad/covector map; this is the target, not a fitted amplitude.",
    },
    {
        "name": "raw_geometric_solder_map",
        "formula": "L_geom=e_plus E_minus, then u_minus_to_plus=L_geom u_minus",
        "status": "bookkeeping only",
        "admissible_now": False,
        "rule": "Not an optical transport unless L_geom^T eta L_geom=eta and Bianchi K_plus/K_minus compatibility are proved.",
    },
    {
        "name": "relative_velocity_projection",
        "formula": "Q_cross = gamma_-^2 (1 - beta_vec.n_photon)^2 in a local positive orthonormal frame",
        "status": "implemented local formula",
        "admissible_now": False,
        "rule": "Requires source-derived beta fields before use in a survey prediction; PM dimensionless velocities need physical calibration before km/s conversion.",
    },
    {
        "name": "fitted_projection",
        "formula": "Q_cross chosen from lensing data",
        "status": "forbidden shortcut",
        "admissible_now": False,
        "rule": "Would be an artificial fit, not a Janus derivation.",
    },
]


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "description": "Audit of the Janus cross-sector optical projection factor Q_cross.",
        "verdict": (
            "Use Q_cross=1 only as the current equal-projection convention. "
            "Keep Q_cross explicit in final formulas until the relative sector "
            "four-velocity projection and L_minus_to_plus tetrad map are derived."
        ),
        "rows": ROWS,
    }
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")

    lines = [
        "# Lensing Q_cross Audit",
        "",
        payload["description"],
        "",
        "| convention | formula | status | admissible now | rule |",
        "|---|---|---|---|---|",
    ]
    for row in ROWS:
        lines.append(
            f"| `{row['name']}` | {row['formula']} | {row['status']} | "
            f"{row['admissible_now']} | {row['rule']} |"
        )
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
