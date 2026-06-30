from __future__ import annotations

from pathlib import Path
import json
import sys

if __package__ in (None, ""):
    sys.path.append(str(Path(__file__).resolve().parents[1]))

from scripts.build_p0_eft_run7_aps_pin_trace_audit import build_payload as build_run7


REPORT_PATH = Path("outputs/reports/p0_eft_run7_dirac_spectrum_pairing_audit.md")
JSON_PATH = Path("outputs/reports/p0_eft_run7_dirac_spectrum_pairing_audit.json")


def build_payload() -> dict:
    run7 = build_run7()
    return {
        "description": "RUN 7 phase 2: APS boundary Dirac spectrum pairing under Pin-.",
        "frozen_sectors": run7["frozen_sectors"],
        "spectrum_pairing_interface": {
            "lean_module": "P0EFTAPSPinDiracSpectrumPairing",
            "operator": "A_APS",
            "pairing_operator": "Pin- reflection J",
            "core_relation": "{A_APS, J} = 0",
            "nonzero_modes": "lambda <-> -lambda",
            "zero_mode_requirement": "h = 0 or zero modes cancel in APS eta package",
        },
        "logical_arrow": {
            "spectral_pairing": "etaRegularizationFixedByPairing",
            "global_package_consequence": "boundaryEtaZeroModeCancellation",
            "trace_consequence": "eta_H + 2 = 0",
        },
        "theorem_status": {
            "dirac_spectrum_pairing_interface_ready": True,
            "nonzero_pairing_formalized": True,
            "zero_mode_control_proved": False,
            "aps_pin_global_index_package_proved": False,
            "full_cosmology_prediction_ready_no_fit": False,
        },
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT RUN 7 Dirac Spectrum Pairing Audit",
        "",
        payload["description"],
        "",
        "## Spectrum Pairing Interface",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["spectrum_pairing_interface"].items())
    lines.extend(["", "## Logical Arrow"])
    lines.extend(f"- {key}: {value}" for key, value in payload["logical_arrow"].items())
    lines.extend(["", "## Status"])
    lines.extend(f"- {key}: {value}" for key, value in payload["theorem_status"].items())
    lines.append("")
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
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
