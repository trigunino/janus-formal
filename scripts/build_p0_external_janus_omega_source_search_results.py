from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_external_janus_omega_source_search_results.md")
JSON_PATH = Path("outputs/reports/p0_external_janus_omega_source_search_results.json")


def build_payload() -> dict:
    sources = [
        {
            "source": "Petit, Margnat & Zejli 2024 / HAL 2025 bimetric model",
            "url": "https://www.jp-petit.org/papers/cosmo/2025-03-07-HAL-A-bimetric-model-based-on-Andrei-Sakharov%27s-twin-universe-approach.pdf",
            "found": "two metrics, coupled field equations, determinant cross-source factors, Bianchi constraints",
            "missing_for_omega": "no explicit D_u L, Omega_alpha=(D_alpha L)L^{-1}, FW/comoving tetrad, or Omega_u u=0 law",
            "status": "measure-and-bianchi-anchor-only",
        },
        {
            "source": "Petit & D'Agostini 2026 questionable black holes",
            "url": "https://www.jp-petit.org/papers/cosmo/2026-01-12-Journal-of-Modern-Physics-QUESTIONABLE-BLACK-HOLES.pdf",
            "found": "restates two coupled field equations with interaction tensors K/Kbar and action/Bianchi consistency",
            "missing_for_omega": "does not define the cross-solder transport law or Lorentz-gauge Omega residual closure",
            "status": "interaction-tensor-anchor-only",
        },
        {
            "source": "Janus official map/site",
            "url": "https://januscosmologicalmodel.com/map",
            "found": "site navigation and public corpus entry point for Janus model material",
            "missing_for_omega": "no direct equation-level source for D_u L or Omega_u u=0 found from this page",
            "status": "index-only",
        },
        {
            "source": "2026 exact-expansion Janus paper listing",
            "url": "https://www.jp-petit.org/papers/cosmo/2026-Expansion-exact-solution-2014-.pdf",
            "found": "recent Janus expansion-law source relevant to cosmological background",
            "missing_for_omega": "no evidence from search result for local L/Omega transport closure",
            "status": "background-cosmology-only-for-this-gate",
        },
    ]
    search_terms = [
        "Janus D_u L transport tetrad",
        "Janus Fermi-Walker comoving tetrad",
        "Janus Omega Lagrangian S_couple Phi",
        "Janus coupled field equations Bianchi K tensor",
    ]
    return {
        "description": "External Janus source search results for Omega_u u=0 / L transport.",
        "status": "external-search-performed-no-omega-source-found",
        "sources": sources,
        "search_terms": search_terms,
        "external_search_performed": True,
        "source_count": len(sources),
        "external_source_search_omega_transport_audit_available": True,
        "external_source_search_scouple_phi_audit_available": True,
        "b4vol_bianchi_source_found": True,
        "k_tensor_source_found": True,
        "du_l_transport_source_found": False,
        "fermi_walker_source_found": False,
        "scouple_phi_transport_source_found": False,
        "omega_u_zero_source_found": False,
        "source_law_found": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The external search found Janus sources for coupled field equations, "
            "determinant source factors, Bianchi consistency, and K tensors, but not "
            "a source-derived D_u L/Omega_u u=0 transport law."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 External Janus Omega Source Search Results",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"External search performed: {payload['external_search_performed']}",
        "Omega transport audit available: "
        f"{payload['external_source_search_omega_transport_audit_available']}",
        "S_couple/Phi audit available: "
        f"{payload['external_source_search_scouple_phi_audit_available']}",
        f"B4vol/Bianchi source found: {payload['b4vol_bianchi_source_found']}",
        f"K tensor source found: {payload['k_tensor_source_found']}",
        f"D_u L transport source found: {payload['du_l_transport_source_found']}",
        f"Fermi-Walker source found: {payload['fermi_walker_source_found']}",
        f"S_couple/Phi transport source found: {payload['scouple_phi_transport_source_found']}",
        f"Omega_u u=0 source found: {payload['omega_u_zero_source_found']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Sources",
        "",
        "| source | url | found | missing for Omega | status |",
        "|---|---|---|---|---|",
    ]
    for row in payload["sources"]:
        lines.append(
            "| {source} | {url} | {found} | {missing_for_omega} | {status} |".format(**row)
        )
    lines.extend(["", "## Search Terms", ""])
    lines.extend(f"- {term}" for term in payload["search_terms"])
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
