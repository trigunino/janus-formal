from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/bianchi_matter_extension_closure_matrix.md")
JSON_PATH = Path("outputs/reports/bianchi_matter_extension_closure_matrix.json")


def build_payload() -> dict:
    rows = [
        {
            "case": "dust",
            "stress": "T^{mu nu}=rho u^mu u^nu",
            "current": "Lorentz algebraic transport and residual reduction written",
            "open": "source-derived continuity, D L, and connection-force cancellation",
            "closed": False,
        },
        {
            "case": "perfect_fluid_flrw_scalar",
            "stress": "T^{mu nu}=(rho+p)u^mu u^nu+p g^{mu nu}",
            "current": "homogeneous FLRW scalar branch with declared w_cross",
            "open": "non-FLRW/lapse/non-comoving tensor transport and source-derived w_cross",
            "closed": False,
        },
        {
            "case": "anisotropic_stress",
            "stress": "T^{mu nu}=(rho+p)u^mu u^nu+p g^{mu nu}+Pi^{mu nu}",
            "current": "tensor target only",
            "open": "projector transport, Pi tensor map, divergence terms and optical contractions",
            "closed": False,
        },
    ]
    return {
        "description": "Matter-extension closure matrix for Bianchi-compatible Janus transport.",
        "all_matter_cases_closed": False,
        "rows": rows,
        "forbidden_shortcuts": [
            "do not reuse dust closure for pressure",
            "do not reuse scalar perfect-fluid branch for anisotropic stress",
            "do not merge pressure or Pi into Q_cross",
            "do not claim tensor lensing before all matter cases needed by the source are closed",
        ],
        "verdict": (
            "Dust is the only reduced algebraic branch. Perfect-fluid and anisotropic "
            "stress remain extension targets and cannot be replaced by scalar shortcuts."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Bianchi Matter Extension Closure Matrix",
        "",
        payload["description"],
        "",
        f"All matter cases closed: {payload['all_matter_cases_closed']}",
        "",
        "| case | stress | current | open | closed |",
        "|---|---|---|---|---|",
    ]
    for row in payload["rows"]:
        lines.append(
            f"| {row['case']} | `{row['stress']}` | {row['current']} | {row['open']} | {row['closed']} |"
        )
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
