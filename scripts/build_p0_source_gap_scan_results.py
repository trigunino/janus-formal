from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_source_gap_scan_results.md")
JSON_PATH = Path("outputs/reports/p0_source_gap_scan_results.json")


def build_payload() -> dict:
    scans = [
        {
            "target": "L_minus_to_plus / D_alpha L / F_alpha",
            "result": "not-found",
            "closest_anchors": [
                "docs/source_traceability.md:108 working target u_minus_to_plus=L_minus_to_plus u_minus",
                "docs/source_traceability.md:109 special FLRW L_minus_to_plus=I; perturbed/global map open",
                "docs/source_traceability.md:110 raw GL(4) solder map, not Lorentz-admissible without proof",
                "docs/source_cards/M30.md:26 two metric/geodesic families",
                "docs/source_cards/M31.md:24 Janus symplectic group action on torsors",
            ],
            "closure_allowed": False,
        },
        {
            "target": "D log B_4vol cancellation / Bianchi product-rule identities",
            "result": "not-found",
            "closest_anchors": [
                "docs/source_traceability.md:117 D_plus.S_plus=0 and D_minus.S_minus=0 target",
                "docs/source_traceability.md:123 R_plus/R_minus residual scaffold open",
                "docs/source_traceability.md:127 FLRW lapse/volume audit only",
                "docs/source_cards/M15.md:26 determinant-ratio coupled equations",
                "docs/verified_formula_register.md:36 M30 determinant ratio almost unity in Newtonian approximation",
            ],
            "closure_allowed": False,
        },
    ]
    consequences = [
        "F_alpha must be derived as new work or explicitly declared as an axiom branch",
        "D log B_4vol cancellation cannot be claimed from M15/M30 alone",
        "R_plus/R_minus must remain open in the readiness gate",
        "full simulation remains diagnostic_pm_only",
    ]
    return {
        "description": "P0 source-gap scan results for the two current blocker identities.",
        "status": "source-gap-confirmed",
        "local_library_scanned": True,
        "f_alpha_source_found": False,
        "dlogb_cancellation_source_found": False,
        "closure_allowed_from_sources": False,
        "physics_closed": False,
        "prediction_ready": False,
        "scans": scans,
        "consequences": consequences,
        "verdict": (
            "The current local source library does not contain the missing F_alpha or "
            "D log B_4vol cancellation identities. The next step is original derivation "
            "or an explicit axiom branch, not a source citation."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Source-Gap Scan Results",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Local library scanned: {payload['local_library_scanned']}",
        f"F_alpha source found: {payload['f_alpha_source_found']}",
        f"DlogB cancellation source found: {payload['dlogb_cancellation_source_found']}",
        f"Closure allowed from sources: {payload['closure_allowed_from_sources']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Scans",
        "",
    ]
    for scan in payload["scans"]:
        lines.append(f"- {scan['target']}: {scan['result']}")
        lines.append(f"  - closure allowed: {scan['closure_allowed']}")
        lines.extend(f"  - closest: {anchor}" for anchor in scan["closest_anchors"])
    lines.extend(["", "## Consequences", ""])
    lines.extend(f"- {item}" for item in payload["consequences"])
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
