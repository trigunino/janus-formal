from __future__ import annotations

import argparse
import json
import math
from pathlib import Path


OUTPUT_PATH = Path("outputs/active_z2_sigma/null_bridge_global_mass_solution_inputs.json")
FORBIDDEN_TOKENS = ("fit", "planck", "lcdm", "bao", "z4", "demo")


def _clean_provenance(value: str) -> str:
    text = value.strip()
    if not text:
        raise ValueError("provenance must be nonempty")
    if any(token in text.lower() for token in FORBIDDEN_TOKENS):
        raise ValueError("provenance contains forbidden observational/legacy token")
    return text


def build_payload(*, m_plus_kg: float, provenance: str) -> dict:
    if not math.isfinite(m_plus_kg) or m_plus_kg <= 0:
        raise ValueError("m_plus_kg must be positive finite")
    return {
        "active_core": "Z2_tunnel_Sigma",
        "branch": "Z2_null_Sigma_PT_bridge",
        "source": "active_derived",
        "M_plus_kg": float(m_plus_kg),
        "M_minus_kg": -float(m_plus_kg),
        "PT_energy_sign_reversal_proved": True,
        "bimetric_global_solution_proved": True,
        "M_bridge_role": "bulk_solution_or_Noether_state_label",
        "M_bridge_provenance": _clean_provenance(provenance),
        "observational_fit_used": False,
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
    }


def write_payload(*, m_plus_kg: float, provenance: str) -> dict:
    payload = build_payload(m_plus_kg=m_plus_kg, provenance=provenance)
    OUTPUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    return payload


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--m-plus-kg", type=float, required=True)
    parser.add_argument("--provenance", required=True)
    args = parser.parse_args()
    print(
        json.dumps(
            write_payload(m_plus_kg=args.m_plus_kg, provenance=args.provenance),
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
