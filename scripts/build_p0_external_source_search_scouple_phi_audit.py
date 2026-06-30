from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_external_source_search_scouple_phi_audit.md")
JSON_PATH = Path("outputs/reports/p0_external_source_search_scouple_phi_audit.json")


def build_payload() -> dict:
    sources = [
        {
            "id": "2015-ads-lagrangian",
            "title": "Lagrangian derivation of the two coupled field equations in the Janus cosmological model",
            "url": "https://ui.adsabs.harvard.edu/abs/2015Ap%26SS.357...67P/abstract",
            "relevant_content": "bibliographic anchor for a Lagrangian derivation of two coupled Janus field equations",
            "transport_law_status": "not-found-in-search-snippet",
        },
        {
            "id": "2014-mpla-coupled",
            "title": "Cosmological bimetric model with interacting positive and negative masses",
            "url": "https://www.jp-petit.org/papers/cosmo/2014-ModPhysLettA.pdf",
            "relevant_content": "displays coupled Einstein-like field equations and Newtonian interaction limits",
            "transport_law_status": "field-equations-only",
        },
        {
            "id": "2019-progress-consistency",
            "title": "Physical and Mathematical Consistency of the Janus Cosmological Model",
            "url": "https://jp-petit.org/papers/cosmo/2019-Progress-in-Physics-1.pdf",
            "relevant_content": "states JCM is based on a system of two coupled field equations and Lagrangian setup",
            "transport_law_status": "field-equations-only",
        },
        {
            "id": "2024-hal-consistency",
            "title": "Janus Cosmological Model Mathematically & Physically Consistent",
            "url": "https://hal.science/hal-04583560v1/document",
            "relevant_content": "recent bimetric model presentation with positive and negative masses",
            "transport_law_status": "no-explicit-L-or-Omega-law-found",
        },
        {
            "id": "2025-sakharov-bimetric",
            "title": "A bimetric cosmological model based on Andrei Sakharov's twin universe approach",
            "url": "https://www.jp-petit.org/papers/cosmo/2025-03-07-HAL-A-bimetric-model-based-on-Andrei-Sakharov%27s-twin-universe-approach.pdf",
            "relevant_content": "summarizes Janus as distinct metrics with distinct field equations",
            "transport_law_status": "no-explicit-L-or-Omega-law-found",
        },
    ]
    exact_search_terms = [
        '"S_couple" "Janus"',
        '"Phi_bar" "Janus Cosmological Model"',
        '"Omega_u" "Janus"',
        '"D_u L" "Janus" "cosmological"',
    ]
    blockers = [
        "external sources found coupled field equations, not the local S_couple/Phi/Phi_bar notation",
        "no explicit variational equation for D_u L transport was found",
        "no source-derived Omega_u u=0 law was found",
        "Phi/Phi_bar remains a local-project notation unless tied to a cited variational source",
        "therefore no prediction closure is allowed",
    ]
    return {
        "description": "Bounded external source audit for Janus S_couple/Phi/Phi_bar and coupled field equations relevant to L/Omega transport.",
        "status": "external-source-search-scouple-phi-open",
        "scope": "bounded web/PDF search with citations; no new law and no prediction",
        "search_date": "2026-06-25",
        "exact_search_terms": exact_search_terms,
        "sources": sources,
        "source_count": len(sources),
        "external_search_performed": True,
        "coupled_field_equation_sources_found": True,
        "scouple_phi_source_found": False,
        "explicit_variational_transport_law_found": False,
        "omega_u_zero_source_law_found": False,
        "physics_closed": False,
        "prediction_ready": False,
        "prediction_claim": False,
        "blockers": blockers,
        "verdict": (
            "The bounded external audit found citable Janus coupled-field-equation sources, "
            "but did not find an explicit variational transport law deriving D_u L/Omega transport "
            "or Omega_u u=0. Closure and prediction remain false."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 External Source Search S_couple/Phi Audit",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Scope: {payload['scope']}",
        f"Search date: {payload['search_date']}",
        f"External search performed: {payload['external_search_performed']}",
        f"Coupled field equation sources found: {payload['coupled_field_equation_sources_found']}",
        f"S_couple/Phi source found: {payload['scouple_phi_source_found']}",
        f"Explicit variational transport law found: {payload['explicit_variational_transport_law_found']}",
        f"Omega_u u=0 source law found: {payload['omega_u_zero_source_law_found']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        f"Prediction claim: {payload['prediction_claim']}",
        "",
        "## Exact Searches",
        "",
    ]
    lines.extend(f"- {term}" for term in payload["exact_search_terms"])
    lines.extend(
        [
            "",
            "## Sources",
            "",
            "| id | title | URL | relevant content | transport law status |",
            "|---|---|---|---|---|",
        ]
    )
    for row in payload["sources"]:
        lines.append(
            "| {id} | {title} | {url} | {relevant_content} | {transport_law_status} |".format(
                **row
            )
        )
    lines.extend(["", "## Blockers", ""])
    lines.extend(f"- {item}" for item in payload["blockers"])
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
