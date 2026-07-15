from __future__ import annotations

import json
import os
from pathlib import Path


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))

GWTC3_GRAVITON_MASS_EV = 1.27e-23
GW170817_ONE_MINUS_CT_MIN = -7.0e-16
GW170817_ONE_MINUS_CT_MAX = 3.0e-15

SOURCES = {
    "gwtc3": "https://arxiv.org/abs/2112.06861",
    "gw170817_speed": "https://doi.org/10.1103/PhysRevD.108.044023",
}


def audit_candidate(graviton_mass_ev: float, one_minus_ct: float) -> dict:
    if graviton_mass_ev < 0:
        raise ValueError("graviton_mass_ev must be nonnegative")
    return {
        "artifact": "generic_gw_observational_bounds",
        "fit_used": False,
        "candidate": {
            "graviton_mass_ev_c2": graviton_mass_ev,
            "one_minus_ct": one_minus_ct,
        },
        "bounds": {
            "gwtc3_graviton_mass_90pct_ev_c2": GWTC3_GRAVITON_MASS_EV,
            "gw170817_one_minus_ct_interval": [
                GW170817_ONE_MINUS_CT_MIN,
                GW170817_ONE_MINUS_CT_MAX,
            ],
        },
        "passes_mass_bound": graviton_mass_ev <= GWTC3_GRAVITON_MASS_EV,
        "passes_speed_bound": (
            GW170817_ONE_MINUS_CT_MIN
            <= one_minus_ct
            <= GW170817_ONE_MINUS_CT_MAX
        ),
        "sources": SOURCES,
        "scope": (
            "generic external-bound audit; candidate values are not derived "
            "from Janus until GW-P09 and GW-P07/P08 close"
        ),
    }


def write_report() -> dict:
    payload = audit_candidate(0.0, 0.0)
    REPORT_DIR.mkdir(parents=True, exist_ok=True)
    (REPORT_DIR / "gw_observational_bounds.json").write_text(
        json.dumps(payload, indent=2), encoding="utf-8"
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_report(), indent=2))
