"""MF-PBRIDGE-001: minimal dependency map from Program M to Program P."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCES = (
    "docs/program_p_variational_principle.md",
    "JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean",
    "formal/axioms/program_m_foundations.md",
)

DATA = (
    {"id": "PB-CORE-01", "datum": "configuration carrier", "class": "minimal_mathematical_core", "required_by": ["P0", "P-A", "P-C"]},
    {"id": "PB-CORE-02", "datum": "admissible maps or symmetries", "class": "minimal_mathematical_core", "required_by": ["P-B", "P-D", "P-E", "P-F"]},
    {"id": "PB-CORE-03", "datum": "scalar codomain and candidate functionals", "class": "minimal_mathematical_core", "required_by": ["P0", "P-A", "P-C"]},
    {"id": "PB-VAR-01", "datum": "differentiable structure on configuration space", "class": "route_specific", "required_by": ["P-A", "P-C"]},
    {"id": "PB-VAR-02", "datum": "Euler source or one-form", "class": "route_specific", "required_by": ["P-C"]},
    {"id": "PB-VAR-03", "datum": "Helmholtz and variational-cohomology closure", "class": "route_specific", "required_by": ["P-C"]},
    {"id": "PB-PARENT-01", "datum": "parent action or independent specification", "class": "external_selection_input", "required_by": ["P-A"]},
    {"id": "PB-REP-01", "datum": "group representations and invariant scalar pairings", "class": "route_specific", "required_by": ["P-D"]},
    {"id": "PB-GEO-01", "datum": "smooth base, bundles, jets and locality", "class": "route_specific", "required_by": ["P-E"]},
    {"id": "PB-INT-01", "datum": "integration, boundary and globalization data", "class": "route_specific", "required_by": ["P-C", "P-F"]},
    {"id": "PB-REN-01", "datum": "normalization and microscopic finite-part law", "class": "external_selection_input", "required_by": ["P-A", "P-C"]},
    {"id": "PB-JANUS-01", "datum": "PT/Z4, sectors, throat, mapping torus and SpinC data", "class": "janus_specialization", "required_by": ["P-B", "P-D", "P-E", "P-F"]},
)

OUTPUTS = (
    "selected action or action class",
    "Euler--Lagrange equations when an action is supplied or reconstructed",
    "Noether identities under supplied symmetries",
    "residual coupling multiplicities",
)


def run_audit() -> dict[str, object]:
    source_status = {source: (ROOT / source).is_file() for source in SOURCES}
    identifiers = [row["id"] for row in DATA]
    minimal_core = [row["datum"] for row in DATA if row["class"] == "minimal_mathematical_core"]
    forbidden_geometry_words = ("metric", "manifold", "throat", "dimension", "gorge")
    return {
        "program": "MF-PBRIDGE-001",
        "sources": source_status,
        "inputs": list(DATA),
        "outputs_not_inputs": list(OUTPUTS),
        "earliest_non_geometric_bridge": minimal_core,
        "gates": {
            "all_sources_exist": all(source_status.values()),
            "dependency_ids_are_unique": len(identifiers) == len(set(identifiers)),
            "earliest_bridge_does_not_assume_geometry": not any(
                word in datum.lower() for datum in minimal_core for word in forbidden_geometry_words
            ),
            "janus_data_are_not_in_minimal_core": all(
                row["class"] != "minimal_mathematical_core"
                for row in DATA if row["id"].startswith("PB-JANUS")
            ),
            "program_p_outputs_are_not_listed_as_inputs": not any(
                output in {row["datum"] for row in DATA} for output in OUTPUTS
            ),
        },
        "next_target_for_program_m": (
            "derive a configuration carrier, admissible transformations and scalar "
            "observables/functionals before attempting manifold geometry"
        ),
        "boundary": (
            "these data let M reach the entrance of P0; productive action reconstruction "
            "still needs a parent specification or differentiable Euler/Helmholtz data"
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    payload = json.dumps(run_audit(), indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload, encoding="utf-8")
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()
