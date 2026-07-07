from __future__ import annotations

import argparse
import json
import math
from pathlib import Path


OUTPUT_PATH = Path("outputs/active_z2_sigma/null_bridge_llbrane_tension_inputs.json")
FORBIDDEN_TOKENS = ("fit", "planck", "lcdm", "bao", "z4", "demo")


def _clean_provenance(value: str) -> str:
    text = value.strip()
    if not text:
        raise ValueError("provenance must be nonempty")
    lower = text.lower()
    if any(token in lower for token in FORBIDDEN_TOKENS):
        raise ValueError("provenance contains forbidden observational/legacy token")
    return text


def build_payload(*, chi_abs_inverse_m: float, provenance: str) -> dict:
    if not math.isfinite(chi_abs_inverse_m) or chi_abs_inverse_m <= 0:
        raise ValueError("chi_abs_inverse_m must be positive finite")
    return {
        "active_core": "Z2_tunnel_Sigma",
        "branch": "Z2_null_Sigma_PT_bridge",
        "source": "active_derived_llbrane",
        "extension_status": "explicit_LL_brane_source",
        "llbrane_action_accepted": True,
        "horizon_straddling_proved": True,
        "a0": 0.125,
        "chi_LL_sign": "negative",
        "chi_LL_abs_inverse_m": float(chi_abs_inverse_m),
        "chi_LL_provenance": _clean_provenance(provenance),
        "observational_fit_used": False,
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
    }


def write_payload(*, chi_abs_inverse_m: float, provenance: str) -> dict:
    payload = build_payload(
        chi_abs_inverse_m=chi_abs_inverse_m,
        provenance=provenance,
    )
    OUTPUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    return payload


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--chi-abs-inverse-m", type=float, required=True)
    parser.add_argument("--provenance", required=True)
    args = parser.parse_args()
    print(
        json.dumps(
            write_payload(
                chi_abs_inverse_m=args.chi_abs_inverse_m,
                provenance=args.provenance,
            ),
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
