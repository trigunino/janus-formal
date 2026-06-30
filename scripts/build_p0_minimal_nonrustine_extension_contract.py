from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_zero_axiom_closure_decision_gate import build_payload as build_decision


REPORT_PATH = Path("outputs/reports/p0_minimal_nonrustine_extension_contract.md")
JSON_PATH = Path("outputs/reports/p0_minimal_nonrustine_extension_contract.json")


def build_payload() -> dict:
    decision = build_decision()
    contract_rows = [
        {
            "requirement": "covariant_path_rule",
            "meaning": "select the holonomy path/family by field variables or action data",
            "required": True,
        },
        {
            "requirement": "same_l_stack",
            "meaning": "one L must feed K, Q_cross, Vlasov moments, and mirror inverse",
            "required": True,
        },
        {
            "requirement": "no_observational_fit",
            "meaning": "no survey/lensing residual may choose path, amplitude, or branch",
            "required": True,
        },
        {
            "requirement": "bianchi_noether_closure",
            "meaning": "new equations must close divergence and split Noether rows",
            "required": True,
        },
        {
            "requirement": "stability_screen",
            "meaning": "principal symbol, ghost, tachyon, and boundary modes must pass",
            "required": True,
        },
        {
            "requirement": "source_traceability",
            "meaning": "extension must cite its axiom/action and not masquerade as published Janus",
            "required": True,
        },
    ]
    return {
        "description": (
            "Anti-rustine contract for a possible future Janus extension. This does "
            "not adopt an axiom; it defines the minimum requirements if zero-axiom "
            "closure remains unavailable."
        ),
        "status": "minimal-nonrustine-extension-contract-not-adopted",
        "decision_status": decision["status"],
        "contract_rows": contract_rows,
        "new_axiom_adopted": False,
        "extension_allowed_only_if_zero_axiom_fails": True,
        "must_be_declared_as_extension": True,
        "can_be_used_for_prediction_now": False,
        "forbids_qdet_qcross_absorption": True,
        "forbids_lensing_fit_selection": True,
        "requires_same_l": True,
        "requires_mirror_inverse": True,
        "requires_stability": True,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "If an extension is eventually needed, this contract prevents a hidden "
            "rustine: it must be explicit, covariant, same-L, unfitted, stable, and "
            "traceable. It is not adopted here."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Minimal Non-Rustine Extension Contract",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"New axiom adopted: {payload['new_axiom_adopted']}",
        f"Extension allowed only if zero-axiom fails: {payload['extension_allowed_only_if_zero_axiom_fails']}",
        f"Must be declared as extension: {payload['must_be_declared_as_extension']}",
        f"Can be used for prediction now: {payload['can_be_used_for_prediction_now']}",
        f"Forbids Qdet/Qcross absorption: {payload['forbids_qdet_qcross_absorption']}",
        f"Forbids lensing-fit selection: {payload['forbids_lensing_fit_selection']}",
        f"Requires same L: {payload['requires_same_l']}",
        f"Requires mirror inverse: {payload['requires_mirror_inverse']}",
        f"Requires stability: {payload['requires_stability']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| requirement | meaning | required |",
        "|---|---|---:|",
    ]
    for row in payload["contract_rows"]:
        lines.append(f"| {row['requirement']} | {row['meaning']} | {row['required']} |")
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
