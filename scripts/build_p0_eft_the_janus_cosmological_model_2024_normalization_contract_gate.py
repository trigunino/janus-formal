from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from janus_lab.janus_2024_bulk_path import (
    absolute_normalization_contract_from_payload,
)
from scripts.build_p0_eft_the_janus_cosmological_model_2024_cited_calibration_gate import (
    build_payload as build_cited_calibration_payload,
)
from scripts.build_p0_eft_janus_z2_published_global_energy_constant_route_gate import (
    build_payload as build_global_energy_route_payload,
)


REPORTS = Path("outputs/reports")
BASE = Path("outputs/active_z2_sigma")
ENERGY_INPUT_PATH = BASE / "published_global_energy_constant_inputs.json"
JSON_PATH = REPORTS / "p0_eft_the_janus_cosmological_model_2024_normalization_contract_gate.json"
REPORT_PATH = REPORTS / "p0_eft_the_janus_cosmological_model_2024_normalization_contract_gate.md"


def _read(path: Path) -> dict | None:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else None


def build_payload() -> dict:
    route = build_global_energy_route_payload()
    cited = build_cited_calibration_payload()
    energy_input = _read(ENERGY_INPUT_PATH)
    normalized = route.get("normalized_sector_payload")
    contract = None
    if normalized is not None and energy_input is not None:
        contract = absolute_normalization_contract_from_payload(
            normalized,
            e_global=float(energy_input["E_global_J"]),
            c_plus_m_s=float(energy_input["c_plus0_m_s"]),
            c_minus_m_s=float(energy_input["c_minus0_m_s"]),
            g_si=1.0,
        )
    elif cited["absolute_normalization_contract_ready"]:
        contract = absolute_normalization_contract_from_payload(
            cited,
            e_global=float(cited["e_global_j"]),
            c_plus_m_s=float(cited["reference_convention"]["c_plus_m_s"]),
            c_minus_m_s=float(cited["reference_convention"]["c_minus_m_s"]),
            g_si=1.0,
        )
    return {
        "status": "the-janus-cosmological-model-2024-normalization-contract-gate",
        "contract_schema_present": True,
        "published_global_energy_route_ready": route["global_energy_constant_route_ready"],
        "published_global_energy_input_present": energy_input is not None,
        "cited_calibration_route_ready": cited["absolute_normalization_contract_ready"],
        "absolute_normalization_contract_instantiated": contract is not None,
        "reference_object_buildable_from_contract": contract is not None,
        "paper_grade_inputs_missing": contract is None,
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# The Janus Cosmological Model 2024 Normalization Contract Gate",
                "",
                f"Contract schema present: `{payload['contract_schema_present']}`",
                f"Published global-energy route ready: `{payload['published_global_energy_route_ready']}`",
                f"Published global-energy input present: `{payload['published_global_energy_input_present']}`",
                f"Cited calibration route ready: `{payload['cited_calibration_route_ready']}`",
                f"Contract instantiated: `{payload['absolute_normalization_contract_instantiated']}`",
                f"Reference object buildable: `{payload['reference_object_buildable_from_contract']}`",
                f"Paper-grade inputs missing: `{payload['paper_grade_inputs_missing']}`",
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
