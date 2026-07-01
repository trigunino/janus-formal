from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_immirzi_perturbation_terms_derivation.md")
JSON_PATH = Path("outputs/reports/p0_eft_immirzi_perturbation_terms_derivation.json")


def build_payload() -> dict:
    terms = [
        {
            "name": "momentum_constraint_sigma_etak",
            "symbol": "S_q = c_q * theta_I(a) * dgq",
            "camb_target": "ayprime(ix_etak) and sigma constraint",
            "conservation_role": "keeps Bianchi momentum constraint consistent with boosted background",
            "derived": False,
        },
        {
            "name": "anisotropic_stress_dgpi",
            "symbol": "S_pi = c_pi * theta_I(a) * dgpi",
            "camb_target": "dgpi, diff_rhopi, sigmadot",
            "conservation_role": "compensates Weyl/shear deformation from Immirzi stress",
            "derived": False,
        },
        {
            "name": "photon_baryon_slip",
            "symbol": "S_slip = c_slip * theta_I(a) * (vb - 3*qg/4)",
            "camb_target": "tight-coupling slip, qgdot, vbdot",
            "conservation_role": "keeps photon-baryon Euler exchange compatible with modified gravity",
            "derived": False,
        },
    ]
    return {
        "description": "Symbolic derivation scaffold for the missing Immirzi perturbation terms.",
        "status": "immirzi-perturbation-terms-derivation-scaffolded",
        "activation_profile": "theta_I(a) = 0.5 * Delta_I * (1 - tanh((a - a_drag)/width))",
        "required_delta_I": 0.09778424139658529,
        "terms": terms,
        "all_terms_derived": all(term["derived"] for term in terms),
        "cambridge_safe_to_patch": False,
        "next_required": (
            "Derive c_q, c_pi and c_slip from the linearized Holst/Immirzi stress tensor. "
            "Until then the CAMB fork must keep Immirzi amplitudes inactive."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Immirzi Perturbation Terms Derivation",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"All terms derived: {payload['all_terms_derived']}",
        f"CAMB safe to patch: {payload['cambridge_safe_to_patch']}",
        "",
        "## Activation",
        "",
        f"- profile: `{payload['activation_profile']}`",
        f"- Delta_I: `{payload['required_delta_I']}`",
        "",
        "| term | symbolic form | CAMB target | derived |",
        "|---|---|---|---:|",
    ]
    for term in payload["terms"]:
        lines.append(
            f"| {term['name']} | `{term['symbol']}` | {term['camb_target']} | {term['derived']} |"
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
