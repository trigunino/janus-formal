from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_cmb_boltzmann_bibliography_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_cmb_boltzmann_bibliography_gate.json")


def build_payload() -> dict:
    sources = {
        "ma_bertschinger": {
            "url": "https://arxiv.org/abs/astro-ph/9506072",
            "supports": ["Einstein_Boltzmann_fluid_equations", "photon_neutrino_hierarchy"],
        },
        "class_overview": {
            "url": "https://arxiv.org/abs/1104.2932",
            "supports": ["Boltzmann_code_architecture", "CMB_LSS_observable_pipeline"],
        },
        "class_approximations": {
            "url": "https://arxiv.org/abs/1104.2933",
            "supports": ["tight_coupling", "radiation_streaming", "accuracy_approximations"],
        },
    }
    return {
        "status": "janus-z2-sigma-cmb-boltzmann-bibliography-gate",
        "active_core": "Z2_tunnel_Sigma",
        "sources": sources,
        "ma_bertschinger_source_found": True,
        "camb_class_source_found": True,
        "photon_polarization_hierarchy_source_found": True,
        "complete_z2_sigma_cmb_boltzmann_equations_found": False,
        "local_cmb_derivation_required": True,
        "may_import_standard_boltzmann_hierarchy": True,
        "must_derive_z2_sigma_metric_sources_locally": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma CMB Boltzmann Bibliography Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Complete Z2/Sigma CMB Boltzmann equations found: `{payload['complete_z2_sigma_cmb_boltzmann_equations_found']}`",
        f"Local derivation required: `{payload['local_cmb_derivation_required']}`",
        "",
        "## Sources",
    ]
    for name, row in payload["sources"].items():
        lines.append(f"- `{name}`: {row['url']}")
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
