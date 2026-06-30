from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_gauge_source_scan_results.md")
JSON_PATH = Path("outputs/reports/p0_gauge_source_scan_results.json")


def build_payload() -> dict:
    scan_results = [
        {
            "track": "Pi eigenframe",
            "source_found": False,
            "closest": [
                "M15 pressure sign convention",
                "FLRW perfect-fluid scalar branch",
                "Pi transport target",
                "Vlasov/Poisson candidate non-dust evolution source",
            ],
            "next": "derive Pi moments from kinetic/Vlasov source or keep Pi branch open",
        },
        {
            "track": "boundary/initial L",
            "source_found": False,
            "closest": [
                "aligned FLRW tetrads give L=I locally",
                "raw geometric solder map target",
                "topology/symmetry material without L transport rule",
            ],
            "next": "build explicit boundary axiom branch or derive L initial data from symmetry",
        },
        {
            "track": "action/gauge principle",
            "source_found": False,
            "closest": [
                "M15 action for coupled field equations",
                "M31 symplectic/torsor group classification",
                "Fermi-Walker/minimal-norm candidate gauges",
            ],
            "next": "new variational principle would be an added axiom unless derived",
        },
    ]
    decision = [
        "no current source closes transverse Omega gauge",
        "boundary/initial L remains first implementation branch because it does not require non-dust matter",
        "Pi branch is physically strong but requires kinetic/moment derivation",
        "action/gauge branch remains highest risk as a new axiom",
    ]
    return {
        "description": "P0 scan results for source anchors that could lift Omega transverse gauge freedom.",
        "status": "gauge-source-scan-open",
        "all_tracks_scanned": True,
        "any_source_found": False,
        "accepted_branch": None,
        "physics_closed": False,
        "prediction_ready": False,
        "scan_results": scan_results,
        "decision": decision,
        "verdict": (
            "No source-derived gauge-lifting rule was found. Continue by deriving a "
            "controlled axiom branch or by extracting Pi from kinetic moments; do not "
            "promote any branch to prediction."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Gauge Source Scan Results",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"All tracks scanned: {payload['all_tracks_scanned']}",
        f"Any source found: {payload['any_source_found']}",
        f"Accepted branch: {payload['accepted_branch']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Scan Results",
        "",
    ]
    for row in payload["scan_results"]:
        lines.append(f"- {row['track']}: source_found={row['source_found']}")
        lines.extend(f"  - closest: {item}" for item in row["closest"])
        lines.append(f"  - next: {row['next']}")
    lines.extend(["", "## Decision", ""])
    lines.extend(f"- {item}" for item in payload["decision"])
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
