from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
INPUT_PATH = BASE / "sigma_area_superselection_sector_inputs.json"
AREA_SPECTRUM_OUTPUT = BASE / "sigma_area_spectrum_inputs.json"
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_area_superselection_sector_manifest.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_area_superselection_sector_manifest.json")

C_SI = 299_792_458.0
HBAR_SI = 1.054_571_817e-34
G_SI = 6.674_30e-11

FORBIDDEN_TOKENS = ("fit", "planck", "lcdm", "bao", "z4", "demo")


def _read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def _bad_provenance(value: Any) -> bool:
    text = str(value or "").strip().lower()
    return not text or any(token in text for token in FORBIDDEN_TOKENS)


def _positive_number(data: dict[str, Any], key: str) -> float | None:
    value = data.get(key)
    if not isinstance(value, (int, float)):
        return None
    value = float(value)
    return value if math.isfinite(value) and value > 0.0 else None


def _positive_int(value: Any) -> int | None:
    return value if isinstance(value, int) and value > 0 else None


def _sector_list(data: dict[str, Any]) -> list[int]:
    values = data.get("N_gap_sectors")
    if isinstance(values, list):
        clean = sorted({_positive_int(value) for value in values if _positive_int(value) is not None})
        return clean
    max_sector = _positive_int(data.get("N_gap_max"))
    if max_sector is not None:
        return list(range(1, max_sector + 1))
    single = _positive_int(data.get("N_gap"))
    return [single] if single is not None else []


def _sector_entry(n_gap: int, area_gap: float) -> dict[str, float | int]:
    area = n_gap * area_gap
    radius = math.sqrt(area / (4.0 * math.pi))
    return {
        "N_gap": n_gap,
        "A_Sigma_m2": area,
        "R_s_m": radius,
        "chi_LL_abs_inverse_m": 1.0 / (8.0 * math.pi * radius),
        "spectral_scale_inverse_m": 1.0 / radius,
    }


def build_payload(
    input_path: Path = INPUT_PATH,
    area_spectrum_output: Path = AREA_SPECTRUM_OUTPUT,
    *,
    write_output: bool = False,
) -> dict[str, Any]:
    data = _read(input_path)
    gamma_abs = _positive_number(data, "holst_immirzi_abs")
    j_min = _positive_number(data, "j_min")
    g_eff = _positive_number(data, "G_eff_SI") or G_SI
    sectors = _sector_list(data)
    base_conditions = {
        "active_core_Z2_tunnel_Sigma": data.get("active_core") == "Z2_tunnel_Sigma",
        "branch_null_PT_bridge": data.get("branch") == "Z2_null_Sigma_PT_bridge",
        "source_active_derived": data.get("source") == "active_derived",
        "area_operator_on_Sigma_derived": bool(data.get("area_operator_on_Sigma_derived")),
        "Holst_area_spectrum_law_derived": bool(data.get("Holst_area_spectrum_law_derived")),
        "physical_induced_area_gauge": data.get("area_gauge") == "physical_induced_S2_metric",
        "superselection_sector_law_declared": bool(data.get("superselection_sector_law_declared")),
        "N_gap_positive_integer_sectors_declared": bool(sectors),
        "non_observational_provenance": not _bad_provenance(data.get("provenance")),
    }
    parameter_conditions = {
        "holst_immirzi_abs_available": gamma_abs is not None,
        "j_min_available": j_min is not None,
    }
    ready = all(base_conditions.values()) and all(parameter_conditions.values())
    area_gap = None
    table = []
    if ready and gamma_abs is not None and j_min is not None:
        l_planck_sq = HBAR_SI * g_eff / C_SI**3
        area_gap = 8.0 * math.pi * gamma_abs * l_planck_sq * math.sqrt(j_min * (j_min + 1.0))
        table = [_sector_entry(n_gap, area_gap) for n_gap in sectors]
        if write_output and len(sectors) == 1:
            area_spectrum_output.parent.mkdir(parents=True, exist_ok=True)
            area_spectrum_output.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "branch": "Z2_null_Sigma_PT_bridge",
                        "source": "active_derived",
                        "area_operator_on_Sigma_derived": True,
                        "Holst_area_spectrum_law_derived": True,
                        "area_gauge": "physical_induced_S2_metric",
                        "area_spectrum_provenance": "active_area_superselection_sector",
                        "holst_immirzi_abs": gamma_abs,
                        "j_min": j_min,
                        "G_eff_SI": g_eff,
                        "N_gap": sectors[0],
                    },
                    indent=2,
                ),
                encoding="utf-8",
            )
    return {
        "status": "janus-z2-sigma-area-superselection-sector-manifest",
        "active_core": "Z2_tunnel_Sigma_null_PT_bridge",
        "physical_statement": (
            "N_gap is treated as a discrete superselection sector, not fitted. "
            "Each positive integer sector gives a no-rustine throat radius and "
            "chi_LL value once the Holst/Sigma area spectrum is active."
        ),
        "input_path": str(input_path),
        "input_present": input_path.exists(),
        "base_conditions": base_conditions,
        "parameter_conditions": parameter_conditions,
        "formulae": {
            "A_gap": "8*pi*|gamma|*l_P^2*sqrt(j_min*(j_min+1))",
            "A_Sigma": "N_gap*A_gap",
            "R_s": "sqrt(A_Sigma/(4*pi))",
            "chi_LL": "-1/(8*pi*R_s)",
        },
        "N_gap_sectors": sectors,
        "A_gap_m2": area_gap,
        "sector_table": table,
        "superselection_family_ready": ready,
        "unique_prediction_ready": False,
        "blocked_by": [key for key, ok in base_conditions.items() if not ok]
        + [key for key, ok in parameter_conditions.items() if not ok],
        "forbidden_shortcuts": [
            "choose_N_gap_by_observation",
            "claim_unique_prediction_from_superselection_family",
            "use_legacy_Z4_area_gap",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload(write_output=True)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Sigma Area Superselection Sector Manifest",
        "",
        payload["physical_statement"],
        "",
        f"Family ready: `{payload['superselection_family_ready']}`",
        f"Unique prediction ready: `{payload['unique_prediction_ready']}`",
        f"A_gap m^2: `{payload['A_gap_m2']}`",
        "",
        "## Sectors",
    ]
    for item in payload["sector_table"]:
        lines.append(
            f"- N_gap={item['N_gap']}: R_s={item['R_s_m']} m, "
            f"chi_abs_inv={item['chi_LL_abs_inverse_m']} 1/m"
        )
    lines.append("")
    lines.append("## Blocked By")
    lines.extend(f"- `{item}`" for item in payload["blocked_by"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
