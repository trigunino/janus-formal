from __future__ import annotations

from pathlib import Path
import json
import os


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))
REPORT_PATH = REPORT_DIR / "p0_cosmology_observable_program.md"
JSON_PATH = REPORT_DIR / "p0_cosmology_observable_program.json"


AXES = {
    "flrw_background": {
        "priority": 1,
        "target": "derive modified Friedmann equations from the orbifold action",
        "required_outputs": [
            "H_plus(a_plus,a_minus)",
            "H_minus(a_plus,a_minus)",
            "Lambda_eff(T_memb,mHR2,v)",
            "cross-sheet source terms",
        ],
        "status": "closed_conditionally_in_minisuperspace",
    },
    "dark_sector_replacement": {
        "priority": 2,
        "target": "map negative-sheet gravity to apparent dark matter and dark energy",
        "required_outputs": [
            "effective dark matter kernel",
            "effective geometric dark energy term",
            "no extra dark particle postulate",
        ],
        "status": "closed_conditionally_in_flrw_effective_map",
    },
    "hubble_tension": {
        "priority": 3,
        "target": "derive redshift-dependent apparent H0 map",
        "required_outputs": [
            "H0_CMB_like",
            "H0_late_like",
            "parameter-free or low-parameter split prediction",
        ],
        "status": "closed_conditionally_as_inference_map",
    },
    "early_structure_jwst": {
        "priority": 4,
        "target": "derive or simulate accelerated primordial collapse",
        "required_outputs": [
            "linear growth equation",
            "collapse-time diagnostic",
            "JWST early massive galaxy observable",
        ],
        "status": "closed_conditionally_as_growth_map",
    },
    "falsifiable_signatures": {
        "priority": 5,
        "target": "derive signatures that differ from GR/Lambda-CDM",
        "required_outputs": [
            "negative-lensing divergence signature",
            "primordial GW transition spectrum",
        ],
        "status": "closed_conditionally_as_signature_map",
    },
}


def build_payload() -> dict:
    return {
        "description": (
            "Observable cosmology program for the Souriau-Janus orbifold candidate."
        ),
        "micro_theory_status": "prediction_ready_true_under_source_certificate",
        "observable_prediction_ready": False,
        "reason_not_ready": (
            "The micro-theory and flat FLRW minisuperspace are gated, but "
            "observable predictions still require dark-sector mapping, H0 mapping, "
            "structure growth, lensing, GW, and likelihood pipeline closure."
        ),
        "first_next_step": "derive_likelihood_pipeline",
        "axes": AXES,
        "hard_blocks": [
            "FLRW minisuperspace is closed conditionally, but not yet calibrated to data",
            "effective dark sector map is closed conditionally, but not yet validated by growth/lensing",
            "H0 inference map is closed conditionally, but not yet fitted to data",
            "early-structure growth equation is closed conditionally as a growth diagnostic",
            "negative-lensing and primordial-GW signatures are mapped conditionally",
            "JWST early-massive galaxy observables are diagnostics only",
            "survey likelihood interface not yet implemented",
            "likelihood/data pipeline not yet implemented",
        ],
        "no_claims": [
            "no claim of solving dark matter yet",
            "no claim of solving dark energy yet",
            "no claim of resolving H0 tension yet",
            "no claim of explaining JWST anomalies yet",
        ],
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Cosmology Observable Program",
        "",
        payload["description"],
        "",
        f"Micro-theory: `{payload['micro_theory_status']}`",
        f"Observable prediction ready: `{payload['observable_prediction_ready']}`",
        f"First next step: `{payload['first_next_step']}`",
        "",
        "## Axes",
        "",
    ]
    for name, axis in payload["axes"].items():
        lines.append(f"### {name}")
        lines.append(f"- priority: `{axis['priority']}`")
        lines.append(f"- target: `{axis['target']}`")
        lines.append(f"- status: `{axis['status']}`")
        for output in axis["required_outputs"]:
            lines.append(f"- required: `{output}`")
        lines.append("")
    lines.extend(["## Hard Blocks", ""])
    for block in payload["hard_blocks"]:
        lines.append(f"- {block}")
    lines.extend(["", "## No Claims", ""])
    for claim in payload["no_claims"]:
        lines.append(f"- {claim}")
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
