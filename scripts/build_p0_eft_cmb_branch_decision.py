from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_cmb_branch_decision.md")
JSON_PATH = Path("outputs/reports/p0_eft_cmb_branch_decision.json")
ROUTE_A_PATH = Path("outputs/reports/p0_eft_torsion_vector_neff_planck_gate.json")
ROUTE_B_PATH = Path("outputs/reports/p0_eft_immirzi_geff_planck_gate.json")


def read_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def build_payload() -> dict:
    route_a = read_json(ROUTE_A_PATH)
    route_b = read_json(ROUTE_B_PATH)
    route_a_excluded = (
        route_a.get("route_a_planck_accepted") is False
        and route_a.get("route_a_improves_planck") is False
    )
    route_b_excluded = (
        route_b.get("route_b_naive_geff_planck_accepted") is False
        and route_b.get("route_b_naive_geff_improves_planck") is False
    )
    return {
        "description": "CMB branch decision after direct Planck gates for simple Janus-Holst early-universe carriers.",
        "status": "cmb-branch-decision-recorded",
        "route_a_free_neff_excluded": route_a_excluded,
        "route_a_required_neff": route_a.get("required_nnu_for_bao_rd"),
        "route_a_chi2_best": (route_a.get("best") or {}).get("chi2_CMB"),
        "route_a_chi2_required_neff": (route_a.get("rows") or [{}, {}])[-1].get("chi2_CMB"),
        "route_b_background_only_excluded": route_b_excluded,
        "route_b_chi2": (route_b.get("trial") or {}).get("chi2_CMB"),
        "cmb_requires_consistent_immirzi_perturbations": route_a_excluded and route_b_excluded,
        "full_cosmology_prediction_ready_no_fit": False,
        "next_required": (
            "Either derive a full Immirzi perturbation-sector patch for CAMB, "
            "or mark the simple Janus-Holst CMB branch as excluded by Planck."
        ),
    }


def render_markdown(payload: dict) -> str:
    return "\n".join(
        [
            "# P0 EFT CMB Branch Decision",
            "",
            payload["description"],
            "",
            f"Status: {payload['status']}",
            f"Full no-fit ready: {payload['full_cosmology_prediction_ready_no_fit']}",
            "",
            "## Decisions",
            "",
            f"- Route A free N_eff excluded: {payload['route_a_free_neff_excluded']}",
            f"- Route B background-only G_eff excluded: {payload['route_b_background_only_excluded']}",
            f"- Requires consistent Immirzi perturbations: {payload['cmb_requires_consistent_immirzi_perturbations']}",
            "",
            "## Evidence",
            "",
            f"- Route A required N_eff: {payload['route_a_required_neff']}",
            f"- Route A best chi2 CMB: {payload['route_a_chi2_best']}",
            f"- Route A required-N_eff chi2 CMB: {payload['route_a_chi2_required_neff']}",
            f"- Route B background-only chi2 CMB: {payload['route_b_chi2']}",
            "",
            "## Next",
            "",
            payload["next_required"],
            "",
        ]
    )


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
