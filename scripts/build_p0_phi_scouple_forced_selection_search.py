from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_phi_scouple_forced_selection_search.md")
JSON_PATH = Path("outputs/reports/p0_phi_scouple_forced_selection_search.json")


def build_payload() -> dict:
    investigation_tracks = [
        {
            "track": "split_noether",
            "question": "Do restored sector diffeomorphisms force a unique Phi/S_couple?",
            "result": "split identities force residual closure only after a two-sector action and on-shell E_phi/E_L; they do not choose Phi",
            "forces_unique": False,
        },
        {
            "track": "flrw_newtonian_tov_limits",
            "question": "Do known limits fix the nonlinear coupling?",
            "result": "limits fix signs, determinant/volume bookkeeping, and special scalar branches but leave nonlinear selector freedom",
            "forces_unique": False,
        },
        {
            "track": "invariant_classification",
            "question": "Do mirror/no-fit/low-derivative constraints leave only one scalar?",
            "result": "local mirror scalar functions of I_metric, det(L), and matter contractions remain admissible",
            "forces_unique": False,
        },
    ]
    remaining_candidate_family = [
        "Phi = c1 I_matter with mirror Phi_bar",
        "Phi = c1 I_matter + c2(I_metric-4)^2 with fixed non-observational constants",
        "Phi = F(I_metric, I_matter) where F has the same weak-field linearization",
        "dust zero-parameter normalized copy branch, still conditional on E_phi/E_L",
    ]
    closure_conditions_needed = [
        "prove split Noether identities before choosing Phi",
        "prove second-order and nonlinear terms vanish or are fixed by Janus source principles",
        "prove low-derivative/locality assumptions are source-mandated, not convenience",
        "prove one candidate alone satisfies pressure/Pi extension and mirror residuals",
    ]
    return {
        "description": "Search for purely internal constraints forcing a unique Phi/S_couple.",
        "status": "forced-selection-not-found",
        "investigation_tracks": investigation_tracks,
        "remaining_candidate_family": remaining_candidate_family,
        "closure_conditions_needed": closure_conditions_needed,
        "split_noether_forces_unique": False,
        "limits_force_unique": False,
        "invariants_force_unique": False,
        "unique_phi_scouple_forced": False,
        "family_obstruction_confirmed": True,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "No internal constraint currently forces a unique Phi/S_couple. The anti-rustine "
            "gate remains closed: adopting A_phi_scouple would be a new axiom, not a derivation."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Phi/S_couple Forced Selection Search",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Split Noether forces unique: {payload['split_noether_forces_unique']}",
        f"Limits force unique: {payload['limits_force_unique']}",
        f"Invariants force unique: {payload['invariants_force_unique']}",
        f"Unique Phi/S_couple forced: {payload['unique_phi_scouple_forced']}",
        f"Family obstruction confirmed: {payload['family_obstruction_confirmed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Investigation Tracks",
        "",
    ]
    for row in payload["investigation_tracks"]:
        lines.append(f"- {row['track']}: {row['question']}")
        lines.append(f"  - result: {row['result']}")
        lines.append(f"  - forces unique: {row['forces_unique']}")
    lines.extend(["", "## Remaining Candidate Family", ""])
    lines.extend(f"- `{item}`" for item in payload["remaining_candidate_family"])
    lines.extend(["", "## Closure Conditions Needed", ""])
    lines.extend(f"- {item}" for item in payload["closure_conditions_needed"])
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
