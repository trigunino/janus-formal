from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_slip_green_neumann_bridge.md")
JSON_PATH = Path("outputs/reports/p0_eft_slip_green_neumann_bridge.json")


def build_payload() -> dict:
    green = {
        "bulk_equation": "(Box_bulk - M_eff^2) S = Source_bnd delta(Sigma), S=Psi-Phi",
        "jump_condition": "Delta(partial_n S)=Source_bnd",
        "green_solution": "S|Sigma = G_Neumann^Sigma * Source_bnd",
        "target_kernel": "G_Neumann^Sigma = (3/2)*H",
        "observable": "lensing sees a kink/derivative jump and an induced boundary value through G_Neumann",
    }
    status_detail = {
        "safe_result": "derivative slip jump is derived",
        "conditional_value_result": "value slip follows if the dS boundary Green kernel equals (3/2)*H",
        "not_done": "explicit dS3 spectral Green integral not computed",
    }
    theorem_status = {
        "neumann_green_bridge_encoded": True,
        "target_kernel_identified": True,
        "green_kernel_computed": False,
        "value_slip_derived_conditionally": True,
        "lensing_source_closed": False,
        "prediction_ready_unconditional": False,
    }
    obligations = [
        "compute the dS3/normal Green kernel for the selected boundary operator",
        "verify G_Neumann^Sigma=(3/2)*H or update the slip coefficient",
        "then propagate S=Psi-Phi to lensing Phi+Psi and growth",
    ]
    return {
        "description": "Green/Neumann bridge from derivative slip jump to boundary slip value.",
        "status": "value-slip-conditional-on-green-kernel",
        "green": green,
        "status_detail": status_detail,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "The mathematically safe observable input is the derivative jump. The value-slip "
            "formula is conditional on the boundary Green kernel; the coefficient (3/2)H "
            "must still be computed or corrected."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Slip Green Neumann Bridge",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## Green",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["green"].items())
    lines.extend(["", "## Detail"])
    lines.extend(f"- {key}: {value}" for key, value in payload["status_detail"].items())
    lines.extend(["", "## Status"])
    lines.extend(f"- {key}: {value}" for key, value in payload["theorem_status"].items())
    lines.extend(["", "## Obligations"])
    lines.extend(f"- {item}" for item in payload["obligations"])
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
