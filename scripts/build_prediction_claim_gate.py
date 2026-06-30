from __future__ import annotations

from pathlib import Path
import json


LENSING_READINESS_PATH = Path("outputs/reports/lensing_readiness_report.json")
SCAFFOLDS_PATH = Path("outputs/reports/remaining_scaffolds_roadmap.json")
OBSERVABLE_CHAIN_PATH = Path("outputs/reports/observable_chain_consistency_audit.json")
SURVEY_INTERFACE_PATH = Path("outputs/reports/survey_likelihood_interface.json")
IC_SOURCE_TARGETS_PATH = Path("outputs/reports/janus_ic_source_targets.json")
PM_BAND_LIMITED_PATH = Path("outputs/reports/pm_band_limited_shear_convergence.json")
PM_CONVERGENCE_COMPARISON_PATH = Path("outputs/reports/pm_convergence_family_comparison.json")
TERMINAL_BLOCKERS_PATH = Path("outputs/reports/p0_terminal_blockers_status.json")
REPORT_PATH = Path("outputs/reports/prediction_claim_gate.md")
JSON_PATH = Path("outputs/reports/prediction_claim_gate.json")


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def load_optional_json(path: Path) -> dict | None:
    return load_json(path) if path.exists() else None


def unique_ordered(items: list[str]) -> list[str]:
    seen = set()
    unique = []
    for item in items:
        if item not in seen:
            seen.add(item)
            unique.append(item)
    return unique


def build_payload(
    lensing: dict,
    scaffolds: dict,
    observable_chain: dict,
    survey_interface: dict,
    ic_source_targets: dict | None = None,
    pm_band_limited: dict | None = None,
    pm_convergence_comparison: dict | None = None,
    physical_rollup: dict | None = None,
) -> dict:
    lensing_blockers = [
        gate["gate"]
        for gate in lensing["gates"]
        if gate["blocks_s8"] and gate["status"] != "closed"
    ]
    scaffold_blockers = [track["track"] for track in scaffolds["tracks"]]
    controlled_pm_ready = bool(
        pm_convergence_comparison
        and pm_convergence_comparison.get("controlled_numerical_convergence_ready", False)
    )
    observable_blockers = []
    if observable_chain["blocking_issue"] and not controlled_pm_ready:
        observable_blockers = ["observable chain convergence"]
    survey_blockers = []
    if not survey_interface.get("survey_layer_ready", False):
        survey_blockers = [
            f"survey {key}"
            for key in survey_interface.get(
                "missing_survey_inputs", ["data vector/covariance"]
            )
        ]
    ic_blockers = []
    if ic_source_targets is not None:
        ic_blockers = [
            f"IC {target['target']}"
            for target in ic_source_targets["missing_source_targets"]
            if target["blocks_final_ic"]
        ]
    pm_band_blockers = []
    if (
        pm_band_limited is not None
        and pm_band_limited.get("blocking_issue", False)
        and not controlled_pm_ready
    ):
        pm_band_blockers = ["PM band-limited shear convergence"]
    physical_blockers = []
    if physical_rollup is None:
        physical_blockers = ["P0 physical rollup missing"]
    else:
        terminal_closed = bool(
            physical_rollup.get(
                "all_terminal_blockers_closed",
                physical_rollup.get("all_blockers_closed", False),
            )
        )
        physics_closed = bool(physical_rollup.get("physics_closed", False))
        physical_prediction_ready = bool(physical_rollup.get("prediction_ready", False))
        if not (terminal_closed and physics_closed and physical_prediction_ready):
            open_items = physical_rollup.get(
                "open_terminal_blockers",
                physical_rollup.get("open_blockers", ["physical P0 blockers open"]),
            )
            physical_blockers = [f"P0 {item}" for item in open_items]
    blockers = unique_ordered([
        *physical_blockers,
        *lensing_blockers,
        *scaffold_blockers,
        *observable_blockers,
        *ic_blockers,
        *pm_band_blockers,
        *(item for item in survey_blockers if item),
    ])
    required_to_upgrade = [
        "close Bianchi-compatible coupled stress tensors",
        "derive Q_det metric-volume map",
        "derive Q_cross projection via L_minus_to_plus compatible with M_minus_to_plus/K_plus and M_plus_to_minus/K_minus",
        "replace IC scaffold with Janus-derived transfer/growth/amplitude/velocity",
        "supply no-fit survey vector, covariance, bins and mask/window",
    ]
    if not controlled_pm_ready:
        required_to_upgrade.insert(
            4,
            "close grid convergence at the claimed observable resolution",
        )
    return {
        "description": "Gate preventing diagnostic Janus outputs from being labelled predictions.",
        "allowed_claim_level": "diagnostic",
        "prediction_ready": len(blockers) == 0,
        "blockers": blockers,
        "required_to_upgrade": required_to_upgrade,
        "verdict": (
            "Diagnostic work may continue, but prediction/proof language is blocked."
            if blockers
            else "Prediction gate is open."
        ),
    }


def build_payload_from_files() -> dict:
    return build_payload(
        load_json(LENSING_READINESS_PATH),
        load_json(SCAFFOLDS_PATH),
        load_json(OBSERVABLE_CHAIN_PATH),
        load_json(SURVEY_INTERFACE_PATH),
        load_json(IC_SOURCE_TARGETS_PATH),
        load_json(PM_BAND_LIMITED_PATH),
        load_json(PM_CONVERGENCE_COMPARISON_PATH),
        load_optional_json(TERMINAL_BLOCKERS_PATH),
    )


def render_markdown(payload: dict) -> str:
    lines = [
        "# Prediction Claim Gate",
        "",
        payload["description"],
        "",
        f"- allowed claim level: {payload['allowed_claim_level']}",
        f"- prediction ready: {payload['prediction_ready']}",
        "",
        "## Blockers",
        "",
    ]
    lines.extend(f"- {item}" for item in payload["blockers"])
    lines.extend(["", "## Required To Upgrade", ""])
    lines.extend(f"- {item}" for item in payload["required_to_upgrade"])
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    return "\n".join(lines)


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload_from_files()
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(render_markdown(payload), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
