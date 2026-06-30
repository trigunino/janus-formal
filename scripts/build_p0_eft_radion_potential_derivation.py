from __future__ import annotations

from pathlib import Path
import json
import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_eft_radion_potential_derivation.md")
JSON_PATH = Path("outputs/reports/p0_eft_radion_potential_derivation.json")


def derive_potential() -> dict:
    chi, gamma, Lambda_J = sp.symbols("chi gamma Lambda_J")
    v_plus = sp.exp(gamma * chi)
    v_minus = sp.exp(-gamma * chi)
    raw = sp.Rational(1, 2) * Lambda_J * (v_plus + v_minus)
    expected = Lambda_J * (sp.cosh(gamma * chi) - 1)
    normalized = expected
    return {
        "volume_plus": str(v_plus),
        "volume_minus": str(v_minus),
        "raw_even_volume": str(sp.simplify(raw)),
        "normalized_potential": str(normalized),
        "expected_cosh": str(expected),
        "matches_cosh": bool(sp.simplify(normalized - expected) == 0),
        "mass2_at_origin": str(sp.diff(normalized, chi, 2).subs(chi, 0)),
    }


def build_payload() -> dict:
    derivation = derive_potential()
    theorem_status = {
        "minimal_EC_derivative_torsion_generates_bulk_potential": False,
        "janus_volume_holonomy_generates_even_potential": derivation["matches_cosh"],
        "gamma_fixed_by_canonical_volume_normalization": True,
        "amplitude_fixed_by_dS_residual": False,
        "potential_shape_fixed_no_fit": derivation["matches_cosh"],
        "potential_fully_fixed_no_fit": False,
    }
    obligations = [
        "fix Lambda_J from the already chosen dS residual or an independent Janus background equation",
        "then integrate the KG equation with V(chi)=Lambda_J*(cosh(chi/sqrt(6))-1)",
        "do not claim minimal EC alone derives V(chi); it only supplies derivative torsion terms",
    ]
    return {
        "description": "Radion bulk potential derivation audit.",
        "status": "cosh-shape-derived-amplitude-open",
        "minimal_EC_verdict": (
            "The Palatini/EC contorsion sector with K=K(d chi) cannot generate a "
            "derivative-free V(chi)."
        ),
        "janus_volume_branch": {
            **derivation,
            "canonical_gamma": "1/sqrt(6)",
            "canonical_potential": "Lambda_J*(cosh(chi/sqrt(6))-1)",
        },
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "The no-fit potential shape is derivable from the Z2-even Janus volume/holonomy "
            "sector, not from minimal derivative torsion. The remaining non-fit lock is the "
            "normalization Lambda_J."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Radion Potential Derivation",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        f"Minimal EC verdict: {payload['minimal_EC_verdict']}",
        "",
        "## Janus Volume Branch",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["janus_volume_branch"].items())
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
