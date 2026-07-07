from __future__ import annotations

import json
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
RHO_PATH = BASE / "rho_plus0_abs_symbolic_closure.json"
GLOBAL_ENERGY_NORMALIZATION_PATH = BASE / "global_energy_constant_sector_normalization_inputs.json"
GRID_PATH = BASE / "sector_metric_on_sigma_inputs.json"
OUTPUT_PATH = BASE / "sector_density_pressure_on_sigma_inputs.json"
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sector_density_pressure_from_rho_plus0_abs_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sector_density_pressure_from_rho_plus0_abs_gate.json")


def _read(path: Path) -> dict[str, Any] | None:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else None


def _grid(payload: dict[str, Any] | None) -> list[float] | None:
    if not payload:
        return None
    values = [float(x) for x in payload["a_grid"]]
    if len(values) < 2 or any(x <= 0.0 for x in values):
        raise ValueError("a_grid must contain positive values")
    if any(b <= a for a, b in zip(values, values[1:], strict=False)):
        raise ValueError("a_grid must be strictly increasing")
    return values


def _select_normalization(
    rho: dict[str, Any] | None,
    global_energy: dict[str, Any] | None,
) -> tuple[dict[str, Any] | None, str | None]:
    if rho is not None and rho.get("rho_plus0_abs_ready") is True:
        return rho, "rho_plus0_abs_symbolic_closure"
    if (
        global_energy is not None
        and global_energy.get("active_core") == "Z2_tunnel_Sigma"
        and global_energy.get("source")
        == "active_derived_from_published_global_energy_constant"
        and "rho_plus0_abs_kg_m3" in global_energy
        and "rho_minus0_abs_kg_m3" in global_energy
    ):
        return global_energy, "published_global_energy_constant"
    return None, None


def build_payload(
    *,
    rho_path: Path = RHO_PATH,
    global_energy_normalization_path: Path = GLOBAL_ENERGY_NORMALIZATION_PATH,
    grid_path: Path = GRID_PATH,
    output_path: Path = OUTPUT_PATH,
    write_output: bool = True,
) -> dict[str, Any]:
    rho = _read(rho_path)
    global_energy = _read(global_energy_normalization_path)
    grid_payload = _read(grid_path)
    errors: list[str] = []
    output = None
    try:
        normalization, normalization_kind = _select_normalization(rho, global_energy)
        if normalization is None:
            errors.append("rho_plus0_abs_or_global_energy_normalization_not_ready")
        grid = _grid(grid_payload)
        if grid is None:
            errors.append("missing_sector_metric_grid")
        if not errors:
            assert normalization is not None and grid is not None
            rho_plus0 = float(normalization["rho_plus0_abs_kg_m3"])
            rho_minus0 = float(normalization["rho_minus0_abs_kg_m3"])
            if rho_plus0 <= 0.0 or rho_minus0 >= 0.0:
                raise ValueError("rho_plus0 must be positive and rho_minus0 must be negative")
            rho_plus = [rho_plus0 * a ** -3 for a in grid]
            rho_minus = [rho_minus0 * a ** -3 for a in grid]
            output = {
                "active_core": "Z2_tunnel_Sigma",
                "source": "active_derived",
                "compressed_planck_lcdm_background_used": False,
                "archived_z4_reuse_used": False,
                "archived_z4_background_reuse_used": False,
                "phenomenological_holst_bao_scan_used": False,
                "observational_H0_fit_used": False,
                "observational_curvature_fit_used": False,
                "sector_density_pressure_on_sigma_ready": True,
                "equation_of_state": "published_bimetric_dust_w0",
                "a_grid": grid,
                "rho_plus_values": rho_plus,
                "p_plus_values": [0.0 for _ in grid],
                "rho_minus_values": rho_minus,
                "p_minus_values": [0.0 for _ in grid],
                "rho_minus0_over_rho_plus0": normalization.get("rho_minus0_over_rho_plus0"),
                "formula": "rho_pm(a)=rho_pm0*a^-3, p_pm(a)=0",
                "normalization_kind": normalization_kind,
                "normalization_source": str(
                    global_energy_normalization_path
                    if normalization_kind == "published_global_energy_constant"
                    else rho_path
                ),
                "grid_source": str(grid_path),
            }
            if write_output:
                output_path.parent.mkdir(parents=True, exist_ok=True)
                output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
    except Exception as exc:
        errors.append(str(exc))
    ready = output is not None and not errors
    return {
        "status": "janus-z2-sector-density-pressure-from-rho-plus0-abs-gate",
        "active_core": "Z2_tunnel_Sigma",
        "rho_manifest_exists": rho is not None,
        "global_energy_normalization_manifest_exists": global_energy is not None,
        "grid_manifest_exists": grid_payload is not None,
        "sector_density_pressure_on_sigma_ready": ready,
        "output_path": str(output_path),
        "blocked_by": errors,
        "gate_passed": ready,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2 Sector Density/Pressure From rho_plus0_abs Gate",
                "",
                f"rho manifest exists: `{payload['rho_manifest_exists']}`",
                f"grid manifest exists: `{payload['grid_manifest_exists']}`",
                f"sector density/pressure ready: `{payload['sector_density_pressure_on_sigma_ready']}`",
                "",
                "## Blocked By",
                *[f"- `{item}`" for item in payload["blocked_by"]],
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
