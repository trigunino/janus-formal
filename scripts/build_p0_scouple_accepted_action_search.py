from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_scouple_accepted_action_search.md")
JSON_PATH = Path("outputs/reports/p0_scouple_accepted_action_search.json")
TEXT_DIR = Path("data/raw/janus_library_text")
M15_TEXT = TEXT_DIR / "M15_lagrangian-derivation-of-the-two-coupled-field-equations-in-the-janus-cosmologic.txt"
M30_TEXT = TEXT_DIR / "M30_a-bimetric-cosmological-model-based-on-andrei-sakharov-s-twin-universe-approach.txt"


def _line_evidence(path: Path, needle: str, window: int = 2) -> dict:
    if not path.exists():
        return {"path": str(path), "needle": needle, "found": False, "line": None, "excerpt": []}
    lines = path.read_text(encoding="utf-8", errors="ignore").splitlines()
    needle_lower = needle.lower()
    for index, line in enumerate(lines):
        if needle_lower in line.lower():
            start = max(0, index - window)
            end = min(len(lines), index + window + 1)
            return {
                "path": str(path),
                "needle": needle,
                "found": True,
                "line": index + 1,
                "excerpt": [item.strip() for item in lines[start:end] if item.strip()],
            }
    return {"path": str(path), "needle": needle, "found": False, "line": None, "excerpt": []}


def build_payload() -> dict:
    evidence = [
        _line_evidence(M15_TEXT, "Now let’s build a bivariation"),
        _line_evidence(M15_TEXT, "δg(+)μν =− δg(−)μν"),
        _line_evidence(M15_TEXT, "Eq. ( 14) as the mathematical"),
        _line_evidence(M30_TEXT, "two-layer action"),
        _line_evidence(M30_TEXT, "interaction tensors"),
        _line_evidence(M30_TEXT, "Bianchi identities"),
    ]
    source_rows = [
        {
            "source": "M15",
            "action_or_principle": (
                "integral of R_plus sqrt(-g_plus)+R_minus sqrt(-g_minus) "
                "-2 chi L_plus sqrt(-g_plus)-2 chi L_minus sqrt(-g_minus)"
            ),
            "accepted_for": "published Lagrangian derivation of Janus coupled field equations",
            "passes": [
                "derives determinant-weighted cross-source field equations under Janus bivariation",
                "keeps pressure in the diagonal perfect-fluid stress form used by the paper",
                "local text extract confirms the constrained variation δg_plus = -δg_minus",
            ],
            "fails_for_scouple": [
                "no independent S_couple functional is supplied",
                "no delta S_couple/delta L equation exists",
                "no Q_cross optical transport map is varied",
                "no split Noether proof gives both R_plus=0 and R_minus=0",
                "no anisotropic-stress Pi transport is derived",
            ],
            "accepted_as_scouple": False,
        },
        {
            "source": "M30",
            "action_or_principle": "modern two-layer action, bimetric field equations, and geodesic presentation",
            "accepted_for": "Janus bimetric/geodesic source anchor, interaction tensors, and Bianchi constraints",
            "passes": [
                "anchors two metric/geodesic families",
                "anchors weak-field interaction signs",
                "local text extract states a two-layer action with interaction tensors",
                "local text extract states Bianchi constraints for source terms",
            ],
            "fails_for_scouple": [
                "does not provide the local S_couple/Phi/L transport functional required by this gate",
                "does not provide pressure/Pi variational closure",
            ],
            "accepted_as_scouple": False,
        },
    ]
    required_acceptance = [
        "source must supply S_couple or explicitly promote it as a new Janus axiom",
        "metric variations must derive K_plus and K_minus",
        "variation with respect to L or the map must derive the same L used by Q_cross",
        "Noether identities must split into both sector residual closures",
        "perfect-fluid pressure and anisotropic stress Pi must be transported as tensors",
        "no observational fit constants or scalar Q_det/Q_cross absorption",
    ]
    return {
        "description": "Search result for an accepted Janus S_couple action that could close split Noether and pressure/Pi.",
        "status": "accepted-scouple-not-found",
        "local_text_sources_available": M15_TEXT.exists() and M30_TEXT.exists(),
        "text_evidence": evidence,
        "source_rows": source_rows,
        "required_acceptance": required_acceptance,
        "closest_published_action": "M15 bivariational total action",
        "m15_action_accepted_for_field_equations": True,
        "m15_action_accepted_as_scouple": False,
        "independent_scouple_found": False,
        "delta_scouple_delta_l_found": False,
        "split_noether_closure_found": False,
        "pressure_pi_variational_closure_found": False,
        "can_use_m15_as_scouple_without_new_axiom": False,
        "requires_new_action_axiom_or_source": True,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The restored M15/M30 texts confirm accepted Janus bivariational/two-layer "
            "actions and Bianchi constraints for the coupled field equations. They still "
            "do not supply the local S_couple/Phi/L transport functional needed to close "
            "split Noether, pressure, or anisotropic-stress Pi transport."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 S_couple Accepted Action Search",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Local text sources available: {payload['local_text_sources_available']}",
        f"Closest published action: {payload['closest_published_action']}",
        f"M15 action accepted for field equations: {payload['m15_action_accepted_for_field_equations']}",
        f"M15 action accepted as S_couple: {payload['m15_action_accepted_as_scouple']}",
        f"Independent S_couple found: {payload['independent_scouple_found']}",
        f"delta S_couple / delta L found: {payload['delta_scouple_delta_l_found']}",
        f"Split Noether closure found: {payload['split_noether_closure_found']}",
        f"Pressure/Pi variational closure found: {payload['pressure_pi_variational_closure_found']}",
        f"Can use M15 as S_couple without new axiom: {payload['can_use_m15_as_scouple_without_new_axiom']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Source Rows",
        "",
    ]
    for row in payload["source_rows"]:
        lines.append(f"- {row['source']}: {row['action_or_principle']}")
        lines.append(f"  - accepted for: {row['accepted_for']}")
        lines.append(f"  - accepted as S_couple: {row['accepted_as_scouple']}")
        lines.extend(f"  - pass: {item}" for item in row["passes"])
        lines.extend(f"  - fail: {item}" for item in row["fails_for_scouple"])
    lines.extend(["", "## Required Acceptance", ""])
    lines.extend(f"- {item}" for item in payload["required_acceptance"])
    lines.extend(["", "## Text Evidence", ""])
    for row in payload["text_evidence"]:
        lines.append(f"- {row['needle']}: found={row['found']} line={row['line']} path={row['path']}")
        for excerpt in row["excerpt"][:3]:
            lines.append(f"  - {excerpt}")
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
