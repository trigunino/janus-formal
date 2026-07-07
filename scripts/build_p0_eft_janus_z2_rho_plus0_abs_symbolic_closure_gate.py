from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
CONSTANTS_PATH = BASE / "early_plasma_codata_constants_inputs.json"
OCCUPATION_PATH = BASE / "projected_occupation_state_inputs.json"
RADIUS_PATH = BASE / "background_curvature_radius_inputs.json"
SECTOR_RATIO_PATH = BASE / "published_bimetric_sector_ratio_inputs.json"
OUTPUT_PATH = BASE / "rho_plus0_abs_symbolic_closure.json"
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_rho_plus0_abs_symbolic_closure_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_rho_plus0_abs_symbolic_closure_gate.json")
MPC_TO_M = 3.0856775814913673e22


def _read(path: Path) -> dict[str, Any] | None:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else None


def _bad_provenance(text: Any) -> bool:
    lowered = str(text or "").lower()
    return any(token in lowered for token in ["fit", "planck", "lcdm", "z4", "bao"])


def _baryon_mass(constants: dict[str, Any] | None) -> float | None:
    if not constants:
        return None
    values = constants.get("constants", constants.get("normalizations", {}))
    value = values.get("baryon_mass_kg")
    return float(value) if value is not None and float(value) > 0.0 else None


def _occupation(occupation: dict[str, Any] | None) -> tuple[float | None, str | None]:
    if not occupation:
        return None, None
    if occupation.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("occupation active_core must be Z2_tunnel_Sigma")
    if occupation.get("source") != "explicit_state_initial_data":
        raise ValueError("occupation source must be explicit_state_initial_data")
    if occupation.get("full_no_fit_prediction_ready") is not False:
        raise ValueError("occupation must remain explicit state data, not no-fit prediction")
    provenance = str(occupation.get("N_occ_provenance", ""))
    if _bad_provenance(provenance):
        raise ValueError("occupation provenance uses forbidden source")
    value = float(occupation["N_occ_Z2Sigma"])
    if value <= 0.0:
        raise ValueError("N_occ_Z2Sigma must be positive")
    return value, provenance


def _radius(radius: dict[str, Any] | None) -> tuple[float | None, str | None]:
    if not radius:
        return None, None
    if radius.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("radius active_core must be Z2_tunnel_Sigma")
    provenance = str(radius.get("scalar_provenance", {}).get("R_curv_Z2Sigma", ""))
    if _bad_provenance(provenance):
        raise ValueError("R_curv provenance uses forbidden source")
    scalars = radius.get("scalars", {})
    if "R_curv_Z2Sigma_m" in scalars:
        value = float(scalars["R_curv_Z2Sigma_m"])
    else:
        value = float(scalars["R_curv_Z2Sigma_Mpc"]) * MPC_TO_M
    if value <= 0.0:
        raise ValueError("R_curv_Z2Sigma must be positive")
    return value, provenance


def _ratio(sector_ratio: dict[str, Any] | None) -> float | None:
    if not sector_ratio:
        return None
    raw = sector_ratio.get("rho_minus0_over_rho_plus0")
    if raw is None:
        raw = sector_ratio.get("normalizations", {}).get("rho_minus0_over_rho_plus0")
    if raw is None:
        return None
    value = float(raw)
    if value >= 0.0:
        raise ValueError("rho_minus0_over_rho_plus0 must be negative")
    return value


def build_payload(
    *,
    constants_path: Path = CONSTANTS_PATH,
    occupation_path: Path = OCCUPATION_PATH,
    radius_path: Path = RADIUS_PATH,
    sector_ratio_path: Path = SECTOR_RATIO_PATH,
    output_path: Path = OUTPUT_PATH,
    write_output: bool = True,
) -> dict[str, Any]:
    errors: list[str] = []
    constants = _read(constants_path)
    occupation_payload = _read(occupation_path)
    radius_payload = _read(radius_path)
    sector_ratio = _read(sector_ratio_path)
    rho_plus = None
    rho_minus = None
    try:
        m_b = _baryon_mass(constants)
        n_occ, n_prov = _occupation(occupation_payload)
        r_curv, r_prov = _radius(radius_payload)
        ratio = _ratio(sector_ratio)
        if m_b is None:
            errors.append("missing_CODATA_baryon_mass")
        if n_occ is None:
            errors.append("missing_N_occ_Z2Sigma")
        if r_curv is None:
            errors.append("missing_R_curv_Z2Sigma")
        if ratio is None:
            errors.append("missing_published_sector_ratio")
        if not errors:
            assert m_b is not None and n_occ is not None and r_curv is not None
            volume = math.pi**2 * r_curv**3
            rho_plus = m_b * n_occ / volume
            rho_minus = ratio * rho_plus if ratio is not None else None
            if write_output:
                output_path.parent.mkdir(parents=True, exist_ok=True)
                output_path.write_text(
                    json.dumps(
                        {
                            "active_core": "Z2_tunnel_Sigma",
                            "source": "active_derived_from_state_and_radius",
                            "rho_plus0_abs_kg_m3": rho_plus,
                            "rho_minus0_abs_kg_m3": rho_minus,
                            "rho_minus0_over_rho_plus0": ratio,
                            "formula": "rho_plus0_abs = m_b*N_occ_Z2Sigma/(pi^2*R_curv_Z2Sigma^3)",
                            "N_occ_provenance": n_prov,
                            "R_curv_provenance": r_prov,
                        },
                        indent=2,
                    ),
                    encoding="utf-8",
                )
    except Exception as exc:
        errors.append(str(exc))
    ready = rho_plus is not None and not errors
    return {
        "status": "janus-z2-rho-plus0-abs-symbolic-closure-gate",
        "active_core": "Z2_tunnel_Sigma",
        "formula_RP3": "rho_plus0_abs = m_b*N_occ_Z2Sigma/(pi^2*R_curv_Z2Sigma^3)",
        "formula_paired_S3": "rho_plus0_abs = m_b*N_occ_Z2Sigma/(2*pi^2*R_curv_Z2Sigma^3)",
        "constants_manifest_exists": constants is not None,
        "occupation_manifest_exists": occupation_payload is not None,
        "radius_manifest_exists": radius_payload is not None,
        "sector_ratio_manifest_exists": sector_ratio is not None,
        "rho_plus0_abs_ready": ready,
        "rho_plus0_abs_kg_m3": rho_plus,
        "rho_minus0_abs_kg_m3": rho_minus,
        "bottom_reached_without_extension": True,
        "remaining_independent_inputs": [] if ready else ["N_occ_Z2Sigma", "R_curv_Z2Sigma"],
        "forbidden_shortcuts": [
            "derive_N_occ_from_Z2_topology_alone",
            "derive_R_curv_from_scale_free_topology_alone",
            "use_observational_omega_b_or_lcdm_density",
        ],
        "validation_errors": errors,
        "gate_passed": ready,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2 rho_plus0_abs Symbolic Closure Gate",
                "",
                f"Formula RP3: `{payload['formula_RP3']}`",
                f"rho_plus0_abs ready: `{payload['rho_plus0_abs_ready']}`",
                f"Remaining independent inputs: `{payload['remaining_independent_inputs']}`",
                f"Bottom reached without extension: `{payload['bottom_reached_without_extension']}`",
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
