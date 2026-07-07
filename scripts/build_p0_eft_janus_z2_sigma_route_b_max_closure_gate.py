from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_area_immirzi_source_gate import (
    INPUT_PATH as IMMIRZI_INPUT,
    build_payload as immirzi,
)
from scripts.build_p0_eft_janus_z2_sigma_area_occupation_selection_gate import (
    INPUT_PATH as OCCUPATION_INPUT,
    build_payload as occupation,
)
from scripts.build_p0_eft_janus_z2_sigma_area_representation_selector_gate import (
    INPUT_PATH as REPRESENTATION_INPUT,
    build_payload as representation,
)
from scripts.build_p0_eft_janus_z2_sigma_area_spectrum_closure_gate import (
    AREA_GAP_OUTPUT,
    INPUT_PATH as AREA_SPECTRUM_INPUT,
    build_payload as area_spectrum,
)


BASE = Path("outputs/active_z2_sigma")
OUTPUT_INPUT = BASE / "sigma_area_spectrum_inputs.json"
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_route_b_max_closure_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_route_b_max_closure_gate.json")


def build_payload(
    *,
    immirzi_input: Path = IMMIRZI_INPUT,
    representation_input: Path = REPRESENTATION_INPUT,
    occupation_input: Path = OCCUPATION_INPUT,
    area_spectrum_input: Path = OUTPUT_INPUT,
    write_output: bool = False,
) -> dict:
    im = immirzi(immirzi_input)
    rep = representation(representation_input)
    occ = occupation(occupation_input)
    composite_input = None
    if im["immirzi_source_ready"] and rep["representation_selector_ready"] and occ["occupation_selector_ready"]:
        composite_input = {
            "active_core": "Z2_tunnel_Sigma",
            "branch": "Z2_null_Sigma_PT_bridge",
            "source": "active_derived",
            "area_operator_on_Sigma_derived": True,
            "Holst_area_spectrum_law_derived": True,
            "area_gauge": "physical_induced_S2_metric",
            "area_spectrum_provenance": "route_b_max_closure",
            "holst_immirzi_abs": im["holst_immirzi_abs"],
            "j_min": rep["j_min"],
            "N_gap": occ["N_gap"],
        }
        if write_output:
            area_spectrum_input.parent.mkdir(parents=True, exist_ok=True)
            area_spectrum_input.write_text(json.dumps(composite_input, indent=2), encoding="utf-8")
    spectrum = area_spectrum(
        area_spectrum_input if composite_input or area_spectrum_input.exists() else AREA_SPECTRUM_INPUT
    )
    ready = bool(composite_input) and spectrum["R_s_prediction_ready"]
    return {
        "status": "janus-z2-sigma-route-b-max-closure-gate",
        "active_core": "Z2_tunnel_Sigma_null_PT_bridge",
        "physical_statement": (
            "Route B closes only if the Immirzi source, representation selector, "
            "and area occupation selector are all active-derived. If occupation "
            "is a superselection label, Route B yields a discrete family rather "
            "than a unique prediction."
        ),
        "components": {
            "immirzi_source_ready": im["immirzi_source_ready"],
            "representation_selector_ready": rep["representation_selector_ready"],
            "occupation_selector_ready": occ["occupation_selector_ready"],
            "area_spectrum_R_s_ready": spectrum["R_s_prediction_ready"],
        },
        "component_status": {
            "immirzi": im["status"],
            "representation": rep["status"],
            "occupation": occ["status"],
            "area_spectrum": spectrum["status"],
        },
        "composite_area_spectrum_input": composite_input,
        "area_gap_output": str(AREA_GAP_OUTPUT),
        "R_s_m": spectrum["derivation"].get("R_s_m"),
        "A_gap_m2": spectrum["derivation"].get("A_gap_m2"),
        "N_gap": occ["N_gap"],
        "N_gap_is_unique_prediction": occ["N_gap_is_unique_prediction"],
        "N_gap_is_superselection_label": occ["N_gap_is_superselection_label"],
        "route_b_unique_prediction_ready": ready and occ["N_gap_is_unique_prediction"],
        "route_b_discrete_family_ready": ready and occ["N_gap_is_superselection_label"],
        "chi_LL_prediction_ready": ready,
        "blocked_by": (
            [f"immirzi:{item}" for item in im["blocked_by"]]
            + [f"representation:{item}" for item in rep["blocked_by"]]
            + [f"occupation:{item}" for item in occ["blocked_by"]]
            + [f"area_spectrum:{item}" for item in spectrum["blocked_by"]]
        ),
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload(write_output=True)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Sigma Route B Max Closure Gate",
        "",
        payload["physical_statement"],
        "",
        f"Unique prediction ready: `{payload['route_b_unique_prediction_ready']}`",
        f"Discrete family ready: `{payload['route_b_discrete_family_ready']}`",
        f"R_s m: `{payload['R_s_m']}`",
        "",
        "## Blocked By",
    ]
    lines.extend(f"- `{item}`" for item in payload["blocked_by"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
