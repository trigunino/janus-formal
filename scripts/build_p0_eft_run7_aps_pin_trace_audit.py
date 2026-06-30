from __future__ import annotations

from pathlib import Path
import json
import sys

if __package__ in (None, ""):
    sys.path.append(str(Path(__file__).resolve().parents[1]))

from scripts.build_p0_eft_run6_global_topology_scaffold import build_payload as build_run6
from scripts.build_p0_eft_run7_aps_pin_global_index_closure import build_payload as build_aps_global


REPORT_PATH = Path("outputs/reports/p0_eft_run7_aps_pin_trace_audit.md")
JSON_PATH = Path("outputs/reports/p0_eft_run7_aps_pin_trace_audit.json")


def build_payload() -> dict:
    run6 = build_run6()
    aps_global = build_aps_global()
    return {
        "description": "RUN 7 APS/Pin- trace audit: global index package implies the local Holst lock.",
        "frozen_sectors": {
            "numeric_solver": "untouched",
            "sdss_eboss_tables": "untouched",
            "orbifold_volume_cover": "closed in RUN 8/RUN 10B",
        },
        "aps_pin_global_package": {
            "pin_minus_lift_squared_minus_one": True,
            "aps_boundary_projector_fredholm": True,
            "boundary_eta_zero_mode_cancellation": "global theorem interface",
            "no_parity_anomaly": "global theorem interface",
            "trace_regularization_standard": "derived if global package closes",
        },
        "logical_arrow": {
            "global_input": "apsPinIndexPackageClosed",
            "lean_module": "P0EFTAPSPinTraceGlobalDerivation",
            "spectrum_pairing_module": "P0EFTAPSPinDiracSpectrumPairing",
            "kernel_trivialization_module": "P0EFTAPSPinDiracKernelTrivialization",
            "global_index_closure_module": aps_global["aps_global_index_closure"]["lean_module"],
            "consequence": "standardTraceNormalizationDerived -> eta_H + 2 = 0",
            "local_residual": run6["local_closed"]["nieh_yan_eta_H_plus_2_residual"],
        },
        "theorem_status": {
            "run7_aps_pin_interface_ready": True,
            "dirac_spectrum_pairing_interface_ready": True,
            "dirac_kernel_trivialization_interface_ready": True,
            "zero_mode_control_proved_from_loaded_gap": True,
            "aps_pin_global_index_package_proved": True,
            "eta_H_no_fit_ready_conditionally_on_APS": True,
            "orbifold_cover_global_theorem_proved": False,
            "full_cosmology_prediction_ready_no_fit": False,
        },
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT RUN 7 APS/Pin Trace Audit",
        "",
        payload["description"],
        "",
        "## Frozen Sectors",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["frozen_sectors"].items())
    lines.extend(["", "## APS/Pin Global Package"])
    lines.extend(f"- {key}: {value}" for key, value in payload["aps_pin_global_package"].items())
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
