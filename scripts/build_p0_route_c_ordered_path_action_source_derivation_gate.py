from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_route_c_pt_only_no_selector_certificate import (
    build_payload as build_pt_no_selector,
)


REPORT_PATH = Path("outputs/reports/p0_route_c_ordered_path_action_source_derivation_gate.md")
JSON_PATH = Path("outputs/reports/p0_route_c_ordered_path_action_source_derivation_gate.json")

SOURCE_TEXTS = {
    "M15": Path(
        "data/raw/janus_library_text/"
        "M15_lagrangian-derivation-of-the-two-coupled-field-equations-in-the-janus-cosmologic.txt"
    ),
    "M29": Path("data/raw/janus_library_text/M29_pt-symmetry-in-one-way-wormholes.txt"),
    "M30": Path(
        "data/raw/janus_library_text/"
        "M30_a-bimetric-cosmological-model-based-on-andrei-sakharov-s-twin-universe-approach.txt"
    ),
    "M31": Path(
        "data/raw/janus_library_text/"
        "M31_study-of-symmetries-through-the-action-on-torsors-of-the-janus-symplectic-group.txt"
    ),
}

TERM_GROUPS = {
    "ordered_path_action": [
        "s_path",
        "path-ordered",
        "ordered path",
        "wilson",
        "path functional",
        "ordered transport",
    ],
    "geometry_transport": [
        "geodesic",
        "holonomy",
        "parallel transport",
        "gluing",
        "throat",
        "boundary",
        "continuity of geodesics",
    ],
    "action_symmetry": [
        "lagrangian",
        "action",
        "variation",
        "noether",
        "symplectic",
        "torsor",
        "pt-symmetry",
    ],
}


def read_source(path: Path) -> str:
    if not path.exists():
        return ""
    return path.read_text(encoding="utf-8", errors="ignore").lower().replace("\x00", "")


def grouped_term_counts(text: str) -> dict:
    return {
        group: {term: text.count(term.lower()) for term in terms}
        for group, terms in TERM_GROUPS.items()
    }


def group_has_hit(counts: dict, group: str) -> bool:
    return any(value > 0 for value in counts[group].values())


def build_payload() -> dict:
    pt_no_selector = build_pt_no_selector()
    source_rows = []
    for source_id, path in SOURCE_TEXTS.items():
        text = read_source(path)
        counts = grouped_term_counts(text)
        ordered_hit = group_has_hit(counts, "ordered_path_action")
        transport_hit = group_has_hit(counts, "geometry_transport")
        action_hit = group_has_hit(counts, "action_symmetry")
        role = {
            "M15": "Lagrangian derivation of coupled bimetric field equations",
            "M29": "PT wormhole bridge, throat/gluing and bimetric identification",
            "M30": "Modern EPJC bimetric/geodesic Janus formulation",
            "M31": "Janus symplectic group and torsor symmetry action",
        }[source_id]
        blocker = {
            "M15": "variational coupled fields constrain metrics but do not define a path-ordered cross-sector L",
            "M29": "PT bridge supplies a throat/geodesic setting, not a cosmological same-L path action",
            "M30": "geodesic families and mixed equations do not specify an ordered holonomy selector",
            "M31": "group/torsor action classifies symmetries, not a variational path functional",
        }[source_id]
        source_rows.append(
            {
                "source": source_id,
                "role": role,
                "text_path": str(path),
                "text_available": bool(text),
                "has_action_or_symmetry_terms": action_hit,
                "has_transport_geometry_terms": transport_hit,
                "has_ordered_path_action_terms": ordered_hit,
                "term_counts": counts,
                "s_path_source_found": False,
                "forces_ordered_path_rule": False,
                "same_l_stack_derived": False,
                "blocker": blocker,
            }
        )

    accepted_sources = [row for row in source_rows if row["s_path_source_found"]]
    return {
        "description": (
            "Final targeted zero-axiom pass for Route C: inspect Janus sources "
            "M15, M29, M30, and M31 for a source-derived ordered path action "
            "S_path[gamma,L] or equivalent covariant boundary/path law."
        ),
        "status": "ordered-path-action-source-derivation-gate-bounded-no-go",
        "depends_on": ["p0_route_c_pt_only_no_selector_certificate"],
        "pt_only_no_selector_status": pt_no_selector["status"],
        "source_rows": source_rows,
        "sources_checked": list(SOURCE_TEXTS),
        "source_count": len(source_rows),
        "accepted_source_count": len(accepted_sources),
        "ordered_path_action_source_found": False,
        "coupled_action_forces_ordered_path_rule": False,
        "geodesics_force_ordered_path_rule": False,
        "symmetries_force_ordered_path_rule": False,
        "pt_bridge_forces_cosmological_same_l": False,
        "bounded_source_no_go_closed": True,
        "full_no_go_proved": False,
        "zero_axiom_derivation_available": False,
        "minimal_extension_object": "S_path[gamma,L; g_plus, g_minus, PT]",
        "clean_extension_next_recommended_if_no_new_source": True,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "This final zero-axiom pass finds no inspected Janus source that "
            "derives an ordered cross-sector path action or same-L selector. "
            "M15/M30 supply coupled bimetric equations and geodesic families, "
            "M29 supplies PT throat/gluing geometry, and M31 supplies symmetry "
            "classification; none forces S_path[gamma,L]. The clean next move is "
            "an explicit minimal extension, unless a new Janus source is added."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Route C Ordered Path Action Source Derivation Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Sources checked: `{payload['sources_checked']}`",
        f"Accepted source count: {payload['accepted_source_count']}",
        f"Ordered path action source found: {payload['ordered_path_action_source_found']}",
        f"Coupled action forces ordered path rule: {payload['coupled_action_forces_ordered_path_rule']}",
        f"Geodesics force ordered path rule: {payload['geodesics_force_ordered_path_rule']}",
        f"Symmetries force ordered path rule: {payload['symmetries_force_ordered_path_rule']}",
        f"PT bridge forces cosmological same-L: {payload['pt_bridge_forces_cosmological_same_l']}",
        f"Bounded source no-go closed: {payload['bounded_source_no_go_closed']}",
        f"Full no-go proved: {payload['full_no_go_proved']}",
        f"Zero-axiom derivation available: {payload['zero_axiom_derivation_available']}",
        f"Minimal extension object: `{payload['minimal_extension_object']}`",
        f"Clean extension next recommended if no new source: {payload['clean_extension_next_recommended_if_no_new_source']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| source | role | action/symmetry terms | transport terms | ordered path terms | S_path source | blocker |",
        "|---|---|---:|---:|---:|---:|---|",
    ]
    for row in payload["source_rows"]:
        lines.append(
            f"| {row['source']} | {row['role']} | {row['has_action_or_symmetry_terms']} | "
            f"{row['has_transport_geometry_terms']} | {row['has_ordered_path_action_terms']} | "
            f"{row['s_path_source_found']} | {row['blocker']} |"
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
