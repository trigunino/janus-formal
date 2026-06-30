from __future__ import annotations

from fractions import Fraction
from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_orbifold_holonomy_quantization.md")
JSON_PATH = Path("outputs/reports/p0_eft_orbifold_holonomy_quantization.json")


def build_payload() -> dict:
    visible_volume_quantum = Fraction(2, 1)
    mirror_volume_quantum = Fraction(1, 1)
    a_sigma = visible_volume_quantum / (visible_volume_quantum + mirror_volume_quantum)
    z_sigma = (1 / a_sigma) - 1
    residual = 3 * a_sigma - 2

    return {
        "description": "Z2 de Sitter orbifold holonomy volume quantization for the membrane epoch.",
        "inputs": {
            "visible_volume_quantum": str(visible_volume_quantum),
            "mirror_volume_quantum": str(mirror_volume_quantum),
            "holonomy_ratio_condition": "Vol_+ : Vol_- = 2 : 1",
            "origin_status": "encoded as the minimal Pin-/Z2 orbifold volume quantum",
        },
        "derivation": {
            "a_sigma_formula": "Vol_+/(Vol_+ + Vol_-)",
            "a_sigma": str(a_sigma),
            "z_sigma": str(z_sigma),
            "identity_residual_3a_sigma_minus_2": str(residual),
        },
        "theorem_status": {
            "a_sigma_identity_closed_under_holonomy_volume_quantum": residual == 0,
            "a_sigma_derived_from_orbifold_holonomy": residual == 0,
            "volume_quantum_still_an_input": True,
            "no_fit_lock_ready_from_a_sigma_alone": False,
        },
        "verdict": (
            "The holonomy volume quantum Vol_+:Vol_-=2:1 gives a_sigma=2/3 and "
            "z_sigma=1/2 exactly. The remaining global task is deriving the 2:1 quantum "
            "from the orbifold index/holonomy classification rather than loading it."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Orbifold Holonomy Quantization",
        "",
        payload["description"],
        "",
        "## Inputs",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["inputs"].items())
    lines.extend(["", "## Derivation"])
    lines.extend(f"- {key}: {value}" for key, value in payload["derivation"].items())
    lines.extend(["", "## Status"])
    lines.extend(f"- {key}: {value}" for key, value in payload["theorem_status"].items())
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
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
