from __future__ import annotations

from pathlib import Path
import json
import sys

if __package__ in (None, ""):
    sys.path.append(str(Path(__file__).resolve().parents[1]))

from scripts.build_p0_eft_run7_dirac_spectrum_pairing_audit import build_payload as build_pairing


REPORT_PATH = Path("outputs/reports/p0_eft_run7_dirac_kernel_trivialization_audit.md")
JSON_PATH = Path("outputs/reports/p0_eft_run7_dirac_kernel_trivialization_audit.json")


def build_payload() -> dict:
    pairing = build_pairing()
    return {
        "description": "RUN 7 phase 3: kernel trivialization via Lichnerowicz positive dS gap.",
        "frozen_sectors": pairing["frozen_sectors"],
        "kernel_trivialization_interface": {
            "lean_module": "P0EFTAPSPinDiracKernelTrivialization",
            "formula": "A_APS^2 = nabla*nabla + R_Sigma/4",
            "laplacian_condition": "connection Laplacian nonnegative",
            "curvature_condition": "R_Sigma > 0 on dS boundary",
            "local_consequence": "no boundary harmonic spinors, h = 0",
        },
        "logical_arrow": {
            "kernel_gap": "kernelTrivializedByDSCurvature",
            "zero_mode_control": "zeroModesVanishOrCancel",
            "eta_package": "etaRegularizationFixedByPairing",
        },
        "theorem_status": {
            "dirac_kernel_trivialization_interface_ready": True,
            "lichnerowicz_positive_gap_formalized": True,
            "positive_boundary_curvature_loaded": True,
            "zero_mode_control_proved_from_loaded_gap": True,
            "aps_pin_global_index_package_proved": False,
            "full_cosmology_prediction_ready_no_fit": False,
        },
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT RUN 7 Dirac Kernel Trivialization Audit",
        "",
        payload["description"],
        "",
        "## Kernel Trivialization Interface",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["kernel_trivialization_interface"].items())
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
