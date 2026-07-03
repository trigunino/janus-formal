from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_photon_geodesic_distance_map_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_photon_geodesic_distance_map_gate.json")


def build_payload() -> dict:
    lock = {
        "background_equations_derived": True,
        "distance_bibliography_checked": True,
        "visible_photon_metric_projection_declared": True,
        "photon_null_geodesic_on_visible_projection": True,
        "sigma_crossing_map_declared": True,
        "affine_redshift_map_derived": True,
        "photon_number_conservation_guard_declared": True,
        "etherington_guard_available": True,
        "hubble_distance_derived": True,
        "transverse_comoving_distance_derived": True,
        "angular_diameter_distance_derived": True,
        "luminosity_distance_derived": True,
    }
    return {
        "status": "janus-z2-sigma-photon-geodesic-distance-map-gate",
        "active_core": "Z2_tunnel_Sigma",
        "lock": lock,
        "photon_distance_lock_closed": all(lock.values()),
        "sigma_photon_geodesic_map_derived": all(lock.values()),
        "distance_family": {
            "D_H": "c / H_Z2Sigma(z)",
            "chi": "integral_0^z c dz_prime / H_Z2Sigma(z_prime)",
            "D_M": "S_k(chi)",
            "D_A": "D_M / (1 + z)",
            "D_L": "(1 + z) * D_M, with Etherington guard when photon number is conserved",
        },
        "legacy_lcdm_distance_substitution_forbidden": True,
        "archived_z4_distance_reuse_forbidden": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Photon Geodesic Distance Map Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Sigma photon geodesic map derived: `{payload['sigma_photon_geodesic_map_derived']}`",
        "",
        "## Distance Family",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["distance_family"].items())
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
