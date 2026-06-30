from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_holonomy_path_rule_branch.md")
JSON_PATH = Path("outputs/reports/p0_holonomy_path_rule_branch.json")


def build_payload() -> dict:
    premise = [
        "if R_Omega != 0, transported L depends on the chosen path or path family",
        "K and Q_cross must use the same path/family rule on any retained holonomy branch",
        "the rule must be source-derived before use in Bianchi transport or optical observables",
    ]
    candidate_path_rules = [
        {
            "name": "positive_null_ray",
            "definition": "transport L along the observed g_plus null ray from source to receiver",
            "source_requirements": [
                "source and receiver event selection",
                "sector metric used for the null ray",
                "lens-map convention tying the same ray to Q_cross and K",
            ],
            "loop_consistency": (
                "closed source-receiver-ray loops must return compatible L holonomy "
                "independent of segmentation"
            ),
            "no_fit_constraints": [
                "ray family cannot be chosen per survey bin to tune shear",
                "holonomy amplitude cannot be calibrated against lensing residuals",
            ],
        },
        {
            "name": "matter_worldline",
            "definition": "transport L along a selected matter flow worldline",
            "source_requirements": [
                "which sector's matter flow selects the curve",
                "equations of motion for the transported source",
                "rule for noncomoving or multi-fluid branches",
            ],
            "loop_consistency": (
                "worldline-plus-connector loops must not produce contradictory K and "
                "Q_cross transports"
            ),
            "no_fit_constraints": [
                "flow choice cannot switch to improve local residuals",
                "worldline prescription must be fixed before comparing observables",
            ],
        },
        {
            "name": "geodesic_congruence",
            "definition": "transport L along a source-derived geodesic congruence",
            "source_requirements": [
                "initial hypersurface and tangent distribution",
                "caustic/crossing branch rule",
                "proof that the same congruence feeds K and Q_cross",
            ],
            "loop_consistency": (
                "nearby congruence loops must satisfy a curvature/holonomy identity "
                "rather than introduce arbitrary branch jumps"
            ),
            "no_fit_constraints": [
                "congruence parameters cannot be adjusted after seeing data",
                "caustic branch choices cannot become hidden nuisance fits",
            ],
        },
        {
            "name": "hypersurface_normal",
            "definition": "transport L along normals to a selected foliation",
            "source_requirements": [
                "source-derived foliation scalar or time function",
                "normal orientation and lapse convention",
                "compatibility with optical paths used by Q_cross",
            ],
            "loop_consistency": (
                "normal-then-spatial loops must close consistently with the declared "
                "Omega curvature"
            ),
            "no_fit_constraints": [
                "foliation cannot be picked to minimize residuals",
                "lapse or slicing freedom cannot absorb Q_cross discrepancies",
            ],
        },
    ]
    required_checks = [
        "prove path/family rule from Janus sources, not observational fitting",
        "use the identical path/family rule for K and Q_cross",
        "state loop consistency identities for nonzero R_Omega",
        "reject any branch whose free choices can absorb survey residuals",
    ]
    return {
        "description": "Broad-pass P0 artifact for relative-holonomy path-rule branches.",
        "status": "broad-pass-research-artifact",
        "source_derived": False,
        "physics_closed": False,
        "prediction_ready": False,
        "not_predictive": True,
        "premise": premise,
        "candidate_path_rules": candidate_path_rules,
        "required_checks": required_checks,
        "verdict": (
            "With R_Omega nonzero, L is path/family dependent. The branch remains "
            "non-predictive until one source-derived path rule is fixed, loop "
            "consistency is proved, and the same rule is used for K and Q_cross "
            "without no-fit violations."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Holonomy Path-Rule Branch",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Source derived: {payload['source_derived']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Premise",
        "",
    ]
    lines.extend(f"- {item}" for item in payload["premise"])
    lines.extend(["", "## Candidate Path Rules", ""])
    for rule in payload["candidate_path_rules"]:
        lines.extend(
            [
                f"### {rule['name']}",
                "",
                f"- Definition: {rule['definition']}",
                "- Source requirements:",
            ]
        )
        lines.extend(f"  - {item}" for item in rule["source_requirements"])
        lines.extend(
            [
                f"- Loop consistency: {rule['loop_consistency']}",
                "- No-fit constraints:",
            ]
        )
        lines.extend(f"  - {item}" for item in rule["no_fit_constraints"])
        lines.append("")
    lines.extend(["## Required Checks", ""])
    lines.extend(f"- {item}" for item in payload["required_checks"])
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
