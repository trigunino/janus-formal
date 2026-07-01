from __future__ import annotations

from pathlib import Path
import csv
import json

import numpy as np

try:
    from scripts.build_kids1000_cosebis_contract import (
        cosebis_fits_bytes,
        find_hdu,
        read_binary_table,
        read_fits_hdus,
    )
except ModuleNotFoundError:
    from build_kids1000_cosebis_contract import (
        cosebis_fits_bytes,
        find_hdu,
        read_binary_table,
        read_fits_hdus,
    )

from janus_lab.cosebis import cosebis_vector_from_xi
from janus_lab.weak_lensing_spectra import janus_xi_curves_for_kids_bins, toy_weyl_power


REPORT_PATH = Path("outputs/reports/kids1000_janus_limber_xi_cosebis.md")
JSON_PATH = Path("outputs/reports/kids1000_janus_limber_xi_cosebis.json")
CSV_PATH = Path("outputs/reports/kids1000_janus_limber_xi_cosebis_vector.csv")


def extract_rows() -> tuple[list[dict], list[dict]]:
    fits = cosebis_fits_bytes()
    hdus = read_fits_hdus(fits)
    return read_binary_table(fits, find_hdu(hdus, "En")), read_binary_table(fits, find_hdu(hdus, "NZ_SOURCE"))


def build_payload() -> dict:
    en_rows, nz_rows = extract_rows()
    en_rows = [row for row in en_rows if 1 <= int(row["ANGBIN"]) <= 5]
    theta_arcmin = np.geomspace(0.5, 300.0, 256)
    scaffold_amplitude = 1.0e-18
    xi_plus, xi_minus = janus_xi_curves_for_kids_bins(
        nz_rows,
        theta_arcmin,
        weyl_power=lambda k, z: toy_weyl_power(k, z, amplitude=scaffold_amplitude),
    )
    vector = cosebis_vector_from_xi(theta_arcmin, xi_plus, xi_minus, en_rows, n_max=5)
    rows = [
        {
            "bin1": int(row["BIN1"]),
            "bin2": int(row["BIN2"]),
            "angbin": int(row["ANGBIN"]),
            "janus_limber_cosebis_en": float(value),
        }
        for row, value in zip(en_rows, vector)
    ]
    return {
        "description": "Janus KiDS-1000 xi_+/xi_- Limber-to-COSEBIs scaffold.",
        "status": "janus-limber-xi-cosebis-vector-built",
        "dimension": len(vector),
        "theta_samples": int(theta_arcmin.size),
        "ell_range": [10.0, 1.0e4],
        "weyl_scaffold_amplitude": scaffold_amplitude,
        "tomographic_pair_count": len(xi_plus),
        "same_order_as_kids_en_scale_cut": True,
        "prediction_vector_id": "janus-kids1000-limber-xi-cosebis-parametric-weyl-v1",
        "weyl_power_provenance": "parametric_scaffold",
        "prediction_ready": False,
        "chi2_ready": False,
        "rows": rows,
        "boundary": (
            "This is the technical Limber/Hankel/COSEBIs path. It uses a smooth "
            "parametric Weyl-power scaffold, not a source-derived Janus-Holst "
            "perturbation spectrum, so it must not be used as a KiDS prediction."
        ),
    }


def write_csv(rows: list[dict]) -> None:
    CSV_PATH.parent.mkdir(parents=True, exist_ok=True)
    with CSV_PATH.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def render_markdown(payload: dict) -> str:
    lines = [
        "# KiDS-1000 Janus Limber Xi COSEBIs",
        "",
        payload["description"],
        "",
        f"Status: `{payload['status']}`",
        f"Dimension: `{payload['dimension']}`",
        f"Tomographic pairs: `{payload['tomographic_pair_count']}`",
        f"Same order as KiDS scale-cut En: `{payload['same_order_as_kids_en_scale_cut']}`",
        f"Weyl power provenance: `{payload['weyl_power_provenance']}`",
        f"Prediction ready: `{payload['prediction_ready']}`",
        f"Chi2 ready: `{payload['chi2_ready']}`",
        "",
        "| bin1 | bin2 | mode | En scaffold |",
        "|---:|---:|---:|---:|",
    ]
    for row in payload["rows"][:20]:
        lines.append(
            f"| {row['bin1']} | {row['bin2']} | {row['angbin']} | "
            f"{row['janus_limber_cosebis_en']:.6g} |"
        )
    lines.extend(["", payload["boundary"], ""])
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    write_csv(payload["rows"])
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")
    print(f"Wrote {CSV_PATH}")


if __name__ == "__main__":
    main()
