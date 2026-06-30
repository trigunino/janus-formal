from __future__ import annotations

import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.build_p0_stueckelberg_gauge_slip_branch import build_payload as build_gauge_payload
from scripts.build_p0_stueckelberg_linearized_field_equation_branch import (
    build_payload as build_linearized_payload,
)
from scripts.build_p0_stueckelberg_comoving_scalar_metric_closure_candidate import (
    build_payload as build_restricted_payload,
)
from scripts.build_p0_stueckelberg_source_identity_branch import (
    build_payload as build_source_payload,
)


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_metric_potential_promotion_gate.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_metric_potential_promotion_gate.json")


def build_payload() -> dict:
    linearized = build_linearized_payload()["decision"]
    gauge = build_gauge_payload()["decision"]
    source = build_source_payload()["decision"]
    restricted = build_restricted_payload()["decision"]
    checks = {
        "linearized_00_poisson_normalization_checked": linearized[
            "linearized_00_poisson_normalization_checked"
        ],
        "janus_linearized_field_equation_derived": linearized[
            "janus_linearized_field_equation_derived"
        ],
        "gauge_branch_declared": gauge["gauge_branch_declared"],
        "janus_slip_equation_derived": gauge["janus_slip_equation_derived"],
        "comoving_source_identity_defined": source[
            "source_identity_defined_for_comoving_scalar_branch"
        ],
        "general_source_identity_closed": source["general_source_identity_closed"],
        "pressure_pi_general_case_closed": source["pressure_pi_general_case_closed"],
        "restricted_comoving_scalar_closure_candidate_passed": restricted[
            "restricted_comoving_scalar_closure_candidate_passed"
        ],
        "restricted_branch_promotes_poisson_to_metric": restricted[
            "promotes_poisson_to_metric_for_restricted_branch"
        ],
    }
    promotion_requirements = [
        "Janus linearized field equation derived, not only Poisson-normalized",
        "Janus gauge and slip equation derived, not only zero-Pi scalar branch",
        "source identity closed for the source class used by the simulation",
        "Q_det/Q_cross provenance fixed before optical Weyl/Ricci use",
    ]
    promotable = (
        checks["janus_linearized_field_equation_derived"]
        and checks["janus_slip_equation_derived"]
        and checks["general_source_identity_closed"]
        and checks["pressure_pi_general_case_closed"]
    )
    decision = {
        "metric_potential_promotion_gate_defined": True,
        "weak_field_scalar_diagnostic_available": True,
        "poisson_potential_promotable_for_restricted_comoving_scalar_branch": checks[
            "restricted_branch_promotes_poisson_to_metric"
        ],
        "poisson_potential_promotable_to_metric_potential": promotable,
        "prediction_ready": False,
    }
    return {
        "artifact": "p0_stueckelberg_metric_potential_promotion_gate",
        "status": "metric-potential-promotion-blocked",
        "fit_used": False,
        "free_parameters": [],
        "physics_closed": False,
        "prediction_ready": False,
        "checks": checks,
        "promotion_requirements": promotion_requirements,
        "decision": decision,
    }


def render_markdown(payload: dict) -> str:
    decision = payload["decision"]
    lines = [
        "# P0 Stueckelberg Metric Potential Promotion Gate",
        "",
        f"Status: {payload['status']}",
        f"Fit used: {payload['fit_used']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Checks",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["checks"].items())
    lines.extend(["", "## Promotion Requirements"])
    lines.extend(f"- {item}" for item in payload["promotion_requirements"])
    lines.extend(
        [
            "",
            "## Decision",
            f"Metric potential promotion gate defined: {decision['metric_potential_promotion_gate_defined']}",
            f"Weak-field scalar diagnostic available: {decision['weak_field_scalar_diagnostic_available']}",
            f"Poisson potential promotable for restricted comoving scalar branch: {decision['poisson_potential_promotable_for_restricted_comoving_scalar_branch']}",
            f"Poisson potential promotable to metric potential: {decision['poisson_potential_promotable_to_metric_potential']}",
            f"Prediction ready: {decision['prediction_ready']}",
            "",
        ]
    )
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    payload = build_payload()
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    return payload


if __name__ == "__main__":
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")
