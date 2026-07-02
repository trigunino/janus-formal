from __future__ import annotations

import json
from pathlib import Path

import numpy as np

from janus_lab.z4_regenerative_camb_provider import (
    CosmologyPoint,
    FIELDS,
    generate_camb_gr_rows,
    provenance_manifest,
    write_spectra,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_regenerative_gr_provider.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_regenerative_gr_provider.json")
SPECTRA_PATH = Path("outputs/reports/p0_eft_janus_z4_regenerative_gr_provider_spectra.csv")


def _finite_rows(rows: list[dict[str, float]]) -> bool:
    return all(np.isfinite(float(row[field])) for row in rows for field in FIELDS)


def build_payload() -> dict:
    cosmology = CosmologyPoint()
    rows = generate_camb_gr_rows(cosmology)
    write_spectra(SPECTRA_PATH, rows)
    manifest = provenance_manifest(cosmology=cosmology)
    increasing = all(rows[idx]["ell"] < rows[idx + 1]["ell"] for idx in range(len(rows) - 1))
    positive_auto = all(row["cl_tt"] >= 0.0 and row["cl_ee"] >= 0.0 and row["cl_pp"] >= 0.0 for row in rows)
    required_cache_keys = (
        "theory_vector_hash",
        "cosmology_hash",
        "nuisance_hash",
        "lambda_hash",
        "backend_version",
        "CAMB_version",
        "Z4_delta_version",
    )
    return {
        "status": "janus-z4-regenerative-gr-provider",
        "source_of_spectra": "regenerated",
        "backend_regenerative": True,
        "z4_sector_enabled": False,
        "lambda_T": 0.0,
        "lambda_E": 0.0,
        "spectra_path": str(SPECTRA_PATH),
        "row_count": len(rows),
        "ell_min": rows[0]["ell"],
        "ell_max": rows[-1]["ell"],
        "native_schema_fields": FIELDS,
        "finite_tt_te_ee_pp_produced": _finite_rows(rows),
        "ell_grid_strictly_increasing": increasing,
        "positive_auto_spectra": positive_auto,
        "provenance_manifest": manifest,
        "cache_keys_complete": all(key in manifest and manifest[key] for key in required_cache_keys),
        "no_csv_fixed_theory_vector": manifest["source_of_spectra"] == "regenerated",
        "regenerative_gr_provider_ready": bool(_finite_rows(rows) and increasing and positive_auto),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Regenerative GR Provider",
        "",
        f"Ready: `{payload['regenerative_gr_provider_ready']}`",
        f"Source of spectra: `{payload['source_of_spectra']}`",
        f"Spectra path: `{payload['spectra_path']}`",
        f"Cache keys complete: `{payload['cache_keys_complete']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
