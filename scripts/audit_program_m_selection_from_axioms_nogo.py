"""MF-SEL-002: no-go for selection from an indistinguishing axiom profile."""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path


AXIOMS = (
    "partial_order",
    "exchangeable",
    "projective",
    "iid_atomless_latents",
    "deterministic_a.e._continuous_comparison",
    "coordinate_symmetry",
    "past_future_duality",
    "coordinatewise_factorization",
)

MODELS = {
    "product_order_2d": {"profile": (True,) * len(AXIOMS), "desired": "select"},
    "product_order_3d": {"profile": (True,) * len(AXIOMS), "desired": "reject"},
}


def selector_factorizations() -> list[dict[str, object]]:
    profiles = sorted({model["profile"] for model in MODELS.values()})
    rows = []
    for decisions in itertools.product(("reject", "select"), repeat=len(profiles)):
        selector = dict(zip(profiles, decisions, strict=True))
        outputs = {name: selector[model["profile"]] for name, model in MODELS.items()}
        rows.append(
            {
                "profile_outputs": list(decisions),
                "model_outputs": outputs,
                "matches_desired_selection": all(
                    outputs[name] == model["desired"] for name, model in MODELS.items()
                ),
            }
        )
    return rows


def run_audit() -> dict[str, object]:
    rows = selector_factorizations()
    same_profile = len({model["profile"] for model in MODELS.values()}) == 1
    different_desired = len({model["desired"] for model in MODELS.values()}) > 1
    return {
        "program": "MF-SEL-002",
        "axioms": list(AXIOMS),
        "models": MODELS,
        "all_profile_based_selectors": rows,
        "gates": {
            "models_have_same_axiom_profile": same_profile,
            "desired_decisions_differ": different_desired,
            "no_profile_selector_separates_models": not any(
                row["matches_desired_selection"] for row in rows
            ),
        },
        "theorem_dependency": (
            "MF-OBS-000: an observable factors through a compression iff it is "
            "constant on every compression fibre"
        ),
        "conclusion": (
            "the declared axiom profile cannot select 1+1 over 3D; any successful "
            "entropy optimization needs an additional independently justified constraint"
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
