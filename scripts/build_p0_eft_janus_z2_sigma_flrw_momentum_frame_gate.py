from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_flrw_momentum_frame_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_flrw_momentum_frame_gate.json")


def build_payload() -> dict:
    declared = {
        "FLRW_momentum_frame_bibliography_checked": True,
        "coframe_connection_pullback_gate_declared": True,
        "radial_energy_dispersion_gate_declared": True,
        "plus_orthonormal_frame_declared": True,
        "minus_orthonormal_frame_declared": True,
        "comoving_observer_frame_declared": True,
        "physical_momentum_declared": True,
        "comoving_momentum_declared": True,
        "isotropic_momentum_norm_declared": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "plus_coframe_pullback_ready": False,
        "minus_coframe_pullback_ready": False,
        "plus_comoving_observer_frame_derived": False,
        "minus_comoving_observer_frame_derived": False,
        "plus_momentum_norm_derived": False,
        "minus_momentum_norm_derived": False,
        "plus_FLRW_momentum_frame_derived": False,
        "minus_FLRW_momentum_frame_derived": False,
        "projected_FLRW_momentum_frame_derived": False,
        "FLRW_momentum_frame_ready": False,
    }
    return {
        "status": "janus-z2-sigma-flrw-momentum-frame-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "standard FLRW comoving observer/frame literature",
            "relativistic kinetic theory in tetrad frames",
            "Ma/Bertschinger comoving momentum convention",
            "active coframe/connection pullback gate",
        ],
        "source_links": [
            "https://ned.ipac.caltech.edu/level5/March01/Carroll3/Carroll8.html",
            "https://arxiv.org/abs/astro-ph/9506072",
            "https://ific.uv.es/~pastor/RINO/PREP429.pdf",
        ],
        "bibliography_result": (
            "Standard FLRW kinetic theory supplies the comoving observer frame and "
            "q=a p_physical convention. The active Janus Z2/Sigma model still has to "
            "derive plus/minus orthonormal frames from the Sigma coframe pullback."
        ),
        "declared": declared,
        "closure": closure,
        "formulas": {
            "physical_momentum": "p_hat_i^(pm) measured in the plus/minus orthonormal FLRW frame",
            "comoving_momentum": "q_i^(pm)=a p_hat_i^(pm)",
            "momentum_norm": "|q|^2=delta^ij q_i q_j in the isotropic FLRW frame",
            "projection": "projected frame valid only after plus/minus frames and Z2/Sigma orientation commute",
        },
        "flrw_momentum_frame_ledger_declared": all(declared.values()),
        "flrw_momentum_frame_ready": all(declared.values()) and all(closure.values()),
        "next_required": [
            "pass_coframe_connection_pullback_gate",
            "derive_plus_minus_orthonormal_FLRW_frames",
            "derive_plus_minus_comoving_observer_frames",
            "prove_projected_FLRW_momentum_frame",
            "feed_result_to_Dirac_radial_energy_dispersion_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma FLRW Momentum Frame Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['flrw_momentum_frame_ledger_declared']}`",
        f"Frame ready: `{payload['flrw_momentum_frame_ready']}`",
        "",
        "## Formulas",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["formulas"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
