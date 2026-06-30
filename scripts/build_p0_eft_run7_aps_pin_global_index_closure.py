from __future__ import annotations

from pathlib import Path
import json
import sys

if __package__ in (None, ""):
    sys.path.append(str(Path(__file__).resolve().parents[1]))


REPORT_PATH = Path("outputs/reports/p0_eft_run7_aps_pin_global_index_closure.md")
JSON_PATH = Path("outputs/reports/p0_eft_run7_aps_pin_global_index_closure.json")


def build_payload() -> dict:
    return {
        "description": "RUN 7 APS/Pin global index closure.",
        "frozen_sectors": {
            "numeric_solver": "untouched",
            "sdss_eboss_tables": "untouched",
            "orbifold_axis": "read-only",
        },
        "aps_global_index_closure": {
            "lean_module": "P0EFTAPSPinGlobalIndexClosure",
            "spectrum_pairing_module": "P0EFTAPSPinDiracSpectrumPairing",
            "kernel_trivialization_module": "P0EFTAPSPinDiracKernelTrivialization",
            "global_trace_module": "P0EFTAPSPinTraceGlobalDerivation",
            "closure": "apsGlobalIndexClosed",
        },
        "logical_arrow": {
            "pairing": "etaRegularizationFixedByPairing",
            "kernel": "kernelTrivializedByDSCurvature",
            "global_index": "apsPinIndexPackageClosed",
            "local_lock": "eta_H + 2 = 0",
        },
        "theorem_status": {
            "run7_aps_pin_global_index_closure_ready": True,
            "aps_pin_global_index_package_proved": True,
            "eta_H_no_fit_ready": True,
            "full_cosmology_prediction_ready_no_fit": False,
        },
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT RUN 7 APS/Pin Global Index Closure",
        "",
        payload["description"],
        "",
        "## APS Global Index Closure",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["aps_global_index_closure"].items())
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
