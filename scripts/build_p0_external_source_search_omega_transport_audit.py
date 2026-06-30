from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_external_source_search_omega_transport_audit.md")
JSON_PATH = Path("outputs/reports/p0_external_source_search_omega_transport_audit.json")


def build_payload() -> dict:
    search_queries = [
        "Jean-Pierre Petit Janus D_u L transport Omega_u u=0",
        "Jean-Pierre Petit Janus Fermi-Walker tetrad comoving transport L",
        "Jean-Pierre Petit Janus geodesic source congruence Omega transport",
        "Janus cosmological model L transport tetrad Jean-Pierre Petit",
        "site:arxiv.org Janus Cosmological Model tetrad Fermi Walker",
        '"D_u L" "Janus"',
        '"Omega_u" "Janus"',
    ]
    sources = [
        {
            "id": "jcm_site_summary_bibliography",
            "title": "The Janus cosmological model: a paradigm shift",
            "url": "https://januscosmologicalmodel.com/",
            "relevant_evidence": (
                "Bibliography/summary says JCM uses two metrics and cites the 2024 EPJ C core paper; "
                "no D_u L, L transport, Fermi-Walker, tetrad, or Omega_u u=0 term was found there."
            ),
            "explicit_transport_equation_found": False,
        },
        {
            "id": "jcm_negative_mass_field_equations",
            "title": "Janus cosmology: what is negative mass?",
            "url": "https://januscosmologicalmodel.com/negativemass",
            "relevant_evidence": (
                "Shows the two coupled field equations and states that positive/negative species follow "
                "distinct geodesic families for distinct metrics; this is geodesic evidence, not an L law."
            ),
            "explicit_transport_equation_found": False,
        },
        {
            "id": "epjc_2024_arxiv_2412_04644",
            "title": "A bimetric cosmological model based on Andrei Sakharov's twin universe approach",
            "url": "https://arxiv.org/html/2412.04644v3",
            "relevant_evidence": (
                "States positive masses follow geodesics of a first metric and negative masses a second; "
                "derives an action, coupled field equations, Bianchi identities, and conservation relation. "
                "Search within the source found no Fermi, tetrad, D_u, Omega, or comoving term."
            ),
            "explicit_transport_equation_found": False,
        },
        {
            "id": "hal_2021_jcm_crisis_pdf",
            "title": "The Janus Cosmological Model, an answer to the deep crisis in cosmology",
            "url": "https://hal.science/hal-03427072v1/file/The%20Janus%20Cosmological%20Model%2C%20an%20answer%20to%20the%20deep%20crisis%20in%20cosmology.pdf",
            "relevant_evidence": (
                "Accessible bibliographic/source target for the Janus model; no located snippet gave the "
                "requested Omega/L transport equation."
            ),
            "explicit_transport_equation_found": False,
        },
        {
            "id": "hal_2024_consistency_pdf",
            "title": "Janus Cosmological Model Mathematically & Physically Consistent",
            "url": "https://hal.science/hal-04583560v1/document",
            "relevant_evidence": (
                "Accessible Janus consistency source; search results did not expose an explicit D_u L, "
                "Fermi-Walker/comoving tetrad, or Omega_u u=0 equation."
            ),
            "explicit_transport_equation_found": False,
        },
    ]
    audit_rows = [
        {
            "target": "D_u L transport law",
            "result": "not found",
            "supporting_sources": ["jcm_site_summary_bibliography", "epjc_2024_arxiv_2412_04644"],
            "notes": "No source located an explicit equation fixing D_u L or an equivalent L transport law.",
        },
        {
            "target": "Fermi-Walker/comoving tetrad",
            "result": "not found in Janus/Petit sources",
            "supporting_sources": ["epjc_2024_arxiv_2412_04644"],
            "notes": "Generic Fermi-Walker papers exist, but the bounded Janus search did not connect them to JCM.",
        },
        {
            "target": "L transport",
            "result": "not found",
            "supporting_sources": ["jcm_site_summary_bibliography", "epjc_2024_arxiv_2412_04644"],
            "notes": "Janus sources use metrics, field equations, interaction tensors, and geodesics, not an L-transport closure.",
        },
        {
            "target": "geodesic/source congruence relevant to Omega_u u=0",
            "result": "partial geodesic evidence only",
            "supporting_sources": ["jcm_negative_mass_field_equations", "epjc_2024_arxiv_2412_04644"],
            "notes": "Distinct geodesic families are explicit, but no source congruence equation was found that implies Omega_u u=0.",
        },
    ]
    return {
        "description": "Bounded external Janus/Petit source audit for Omega_u u=0 / L transport.",
        "status": "external-source-search-omega-transport-audit-open",
        "scope": "bounded web search; citations recorded; no closure without explicit equation",
        "search_queries": search_queries,
        "sources": sources,
        "audit_rows": audit_rows,
        "external_search_performed": True,
        "explicit_equation_found": False,
        "source_law_found": False,
        "omega_u_zero_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "prediction_claim": False,
        "verdict": (
            "The bounded search found Janus support for coupled metrics, field equations, Bianchi/conservation, "
            "and distinct geodesic families, but not an explicit source-derived D_u L, L-transport, "
            "Fermi-Walker/comoving tetrad, or Omega_u u=0 equation. Prediction remains false."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 External Source Search Omega Transport Audit",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Scope: {payload['scope']}",
        f"External search performed: {payload['external_search_performed']}",
        f"Explicit equation found: {payload['explicit_equation_found']}",
        f"Source law found: {payload['source_law_found']}",
        f"Omega_u u=0 closed: {payload['omega_u_zero_closed']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        f"Prediction claim: {payload['prediction_claim']}",
        "",
        "## Search Queries",
        "",
    ]
    lines.extend(f"- {query}" for query in payload["search_queries"])
    lines.extend(["", "## Sources", "", "| id | title | url | evidence | explicit transport equation |", "|---|---|---|---|---|"])
    for source in payload["sources"]:
        lines.append(
            "| {id} | {title} | {url} | {relevant_evidence} | {explicit_transport_equation_found} |".format(
                **source
            )
        )
    lines.extend(["", "## Audit Rows", "", "| target | result | sources | notes |", "|---|---|---|---|"])
    for row in payload["audit_rows"]:
        lines.append(
            "| {target} | {result} | {sources} | {notes} |".format(
                target=row["target"],
                result=row["result"],
                sources=", ".join(row["supporting_sources"]),
                notes=row["notes"],
            )
        )
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
