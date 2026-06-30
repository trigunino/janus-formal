from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/pm_convergence_family_comparison.md")
JSON_PATH = Path("outputs/reports/pm_convergence_family_comparison.json")
DEFAULT_REPORTS = [
    Path("outputs/reports/pm_band_limited_shear_convergence.json"),
    Path("outputs/reports/pm_band_limited_shear_convergence_analytic_multimode_fixed_total.json"),
]


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def build_payload(paths: list[Path] = DEFAULT_REPORTS) -> dict:
    rows = []
    for path in paths:
        payload = load_json(path)
        settings = payload.get("run_settings", {})
        rows.append(
            {
                "path": str(path),
                "ic_family": settings.get("ic_family", "unknown"),
                "mass_normalization": settings.get("mass_normalization", "unknown"),
                "displacement_scale": settings.get("displacement_scale"),
                "stable_band_count": payload["stable_band_count"],
                "common_band_count": payload["common_band_count"],
                "blocking_issue": payload["blocking_issue"],
            }
        )
    controlled = [
        row
        for row in rows
        if row["ic_family"] == "analytic-multimode"
        and row["mass_normalization"] == "fixed-total"
        and not row["blocking_issue"]
    ]
    return {
        "description": "Comparison of PM shear convergence diagnostics by IC family.",
        "rows": rows,
        "controlled_numerical_convergence_ready": bool(controlled),
        "canonical_controlled_report": controlled[0]["path"] if controlled else None,
        "verdict": (
            "Controlled numerical convergence is available for analytic-multimode with fixed total mass."
            if controlled
            else "No controlled numerical convergence report is currently stable."
        ),
        "boundary": (
            "Numerical convergence only. This does not close Janus IC derivation, tensor "
            "normalization, Q_det, Q_cross, Bianchi closure, or survey likelihood."
        ),
    }


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# PM Convergence Family Comparison",
        "",
        payload["description"],
        "",
        "| report | IC family | mass normalization | stable bands | blocking |",
        "|---|---|---|---:|---|",
    ]
    for row in payload["rows"]:
        lines.append(
            f"| {row['path']} | {row['ic_family']} | {row['mass_normalization']} | "
            f"{row['stable_band_count']} / {row['common_band_count']} | {row['blocking_issue']} |"
        )
    lines.extend(
        [
            "",
            f"Controlled numerical convergence ready: `{payload['controlled_numerical_convergence_ready']}`.",
            "",
            payload["boundary"],
            "",
            f"Verdict: {payload['verdict']}",
            "",
        ]
    )
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
