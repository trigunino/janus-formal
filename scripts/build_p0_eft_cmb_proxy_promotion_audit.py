from __future__ import annotations

from pathlib import Path
import json

try:
    from scripts.build_p0_eft_direct_cmb_end_to_end_scaffold import build_payload as cmb_proxy_payload
except ModuleNotFoundError:
    from build_p0_eft_direct_cmb_end_to_end_scaffold import build_payload as cmb_proxy_payload


REPORT_PATH = Path("outputs/reports/p0_eft_cmb_proxy_promotion_audit.md")
JSON_PATH = Path("outputs/reports/p0_eft_cmb_proxy_promotion_audit.json")


def build_payload() -> dict:
    proxy = cmb_proxy_payload()
    replacements = [
        {
            "proxy": "weyl_source",
            "current_status": "proxy_ready",
            "replacement_required": "derive Phi/Psi/Weyl transfer from Janus-Holst perturbation equations",
            "validated": False,
        },
        {
            "proxy": "visibility",
            "current_status": "proxy_ready",
            "replacement_required": "derive recombination and drag visibility with Holst Delta_Neff and Janus baryon-photon plasma",
            "validated": False,
        },
        {
            "proxy": "boltzmann_integrator",
            "current_status": "proxy_integrated",
            "replacement_required": "integrate full photon-baryon-neutrino-matter hierarchy",
            "validated": False,
        },
        {
            "proxy": "cl_spectra",
            "current_status": "proxy_computed",
            "replacement_required": "compute TT/TE/EE/lensing spectra with covariance-compatible likelihood vectors",
            "validated": False,
        },
    ]
    all_validated = all(row["validated"] for row in replacements)
    return {
        "description": "Promotion audit from CMB proxy scaffold to direct CMB likelihood.",
        "status": "cmb-proxy-promotion-audit-open",
        "proxy_pipeline_ready": proxy["cl_proxy_computed"],
        "is_planck_verdict": False,
        "direct_cmb_prediction_ready": all_validated,
        "replacements": replacements,
        "open_replacement_count": sum(1 for row in replacements if not row["validated"]),
        "next_required": "replace each proxy kernel with a validated Janus-Holst physical equation before any Planck likelihood.",
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT CMB Proxy Promotion Audit",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Proxy pipeline ready: {payload['proxy_pipeline_ready']}",
        f"Direct CMB prediction ready: {payload['direct_cmb_prediction_ready']}",
        f"Open replacements: {payload['open_replacement_count']}",
        "",
        "| proxy | status | validated | replacement required |",
        "|---|---|---:|---|",
    ]
    for row in payload["replacements"]:
        lines.append(
            f"| {row['proxy']} | {row['current_status']} | {row['validated']} | "
            f"{row['replacement_required']} |"
        )
    lines.extend(["", "## Next", "", payload["next_required"], ""])
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
