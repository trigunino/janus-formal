from __future__ import annotations

import json
import os
from pathlib import Path

import sympy as sp


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))


def build_payload() -> dict:
    compactness = sp.Rational(8, 9)
    root = sp.sqrt(1 - compactness)
    quoted_lapse = sp.Rational(3, 2) * root - sp.Rational(1, 2) * root
    return {
        "artifact": "plugstar_source_equation_audit",
        "source": {
            "doi": "10.4236/jmp.2025.1610072",
            "pdf_pages_checked": [1481, 1482, 1483],
        },
        "exact_checks": {
            "critical_compactness": str(compactness),
            "sqrt_one_minus_compactness": str(root),
            "quoted_redshift_lapse": str(sp.simplify(quoted_lapse)),
            "quoted_wavelength_ratio": str(sp.simplify(1 / quoted_lapse)),
            "critical_radius_over_schwarzschild_radius": str(
                sp.simplify(1 / compactness)
            ),
        },
        "derived_in_source": [
            "constant_density_Schwarzschild_interior",
            "pressure_critical_compactness_8_over_9",
            "quoted_near_critical_redshift_ratio_3",
        ],
        "conjectured_or_missing": [
            "coordinate_speed_interpreted_as_physical_variable_c",
            "quantum_gravitational_mass_inversion",
            "negative_mass_expulsion_dynamics",
            "two_metric_stress_tensors_and_junction_conditions",
            "radial_stability",
            "radiative_transfer_and_EHT_image_forward_model",
        ],
        "co02_ready": False,
        "next_required_atom": (
            "explicit two-sector static field equations plus matter equation "
            "of state and center/interface/boundary conditions"
        ),
    }


def write_report() -> dict:
    payload = build_payload()
    REPORT_DIR.mkdir(parents=True, exist_ok=True)
    (REPORT_DIR / "plugstar_source_equation_audit.json").write_text(
        json.dumps(payload, indent=2), encoding="utf-8"
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_report(), indent=2))
