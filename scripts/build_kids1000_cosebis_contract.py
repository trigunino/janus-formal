from __future__ import annotations

from pathlib import Path
import json
import math
import struct
import tarfile

try:
    from scripts.build_kids1000_data_products_inventory import RAW_TARBALL, fetch_tarball, parse_fits_value
    from scripts.build_survey_data_contract import build_payload as build_contract_payload
except ModuleNotFoundError:
    from build_kids1000_data_products_inventory import RAW_TARBALL, fetch_tarball, parse_fits_value
    from build_survey_data_contract import build_payload as build_contract_payload


REPORT_PATH = Path("outputs/reports/kids1000_cosebis_contract.md")
JSON_PATH = Path("outputs/reports/kids1000_cosebis_contract.json")


def read_fits_hdus(data: bytes) -> list[dict[str, object]]:
    hdus = []
    offset = 0
    while offset + 2880 <= len(data):
        header: dict[str, object] = {}
        cards_read = 0
        while offset + (cards_read + 1) * 80 <= len(data):
            card = data[offset + cards_read * 80 : offset + (cards_read + 1) * 80].decode(
                "ascii",
                errors="ignore",
            )
            cards_read += 1
            key = card[:8].strip()
            if key == "END":
                break
            if card[8:10] == "= ":
                header[key] = parse_fits_value(card[10:])
        if not header and cards_read == 0:
            break
        header_size = int(math.ceil(cards_read * 80 / 2880) * 2880)
        data_start = offset + header_size
        naxis = int(header.get("NAXIS", 0) or 0)
        bitpix = abs(int(header.get("BITPIX", 8) or 8))
        pcount = int(header.get("PCOUNT", 0) or 0)
        gcount = int(header.get("GCOUNT", 1) or 1)
        data_units = 0 if naxis == 0 else 1
        for axis in range(1, naxis + 1):
            data_units *= int(header.get(f"NAXIS{axis}", 0) or 0)
        data_size = ((bitpix // 8) * data_units + pcount) * gcount
        hdus.append(
            {
                "extname": str(header.get("EXTNAME", "PRIMARY")),
                "header": header,
                "data_start": data_start,
                "data_size": data_size,
            }
        )
        offset = data_start + (int(math.ceil(data_size / 2880) * 2880) if data_size else 0)
        if offset >= len(data):
            break
    return hdus


def find_hdu(hdus: list[dict[str, object]], extname: str) -> dict[str, object]:
    for hdu in hdus:
        if str(hdu["extname"]).upper() == extname.upper():
            return hdu
    raise KeyError(f"missing FITS extension {extname}")


def read_image_float64(data: bytes, hdu: dict[str, object]) -> list[list[float]]:
    header = hdu["header"]
    if header.get("BITPIX") != -64:
        raise ValueError("only float64 FITS image HDUs are supported")
    n1 = int(header["NAXIS1"])
    n2 = int(header["NAXIS2"])
    start = int(hdu["data_start"])
    values = struct.unpack(f">{n1 * n2}d", data[start : start + n1 * n2 * 8])
    return [list(values[row * n1 : (row + 1) * n1]) for row in range(n2)]


def table_columns(header: dict[str, object]) -> list[dict[str, object]]:
    columns = []
    offset = 0
    for index in range(1, int(header["TFIELDS"]) + 1):
        name = str(header[f"TTYPE{index}"]).strip()
        form = str(header[f"TFORM{index}"]).strip()
        repeat = int(form[:-1] or "1") if len(form) > 1 else 1
        code = form[-1]
        if code == "K":
            size = 8 * repeat
            fmt = f">{repeat}q"
        elif code == "D":
            size = 8 * repeat
            fmt = f">{repeat}d"
        else:
            raise ValueError(f"unsupported FITS table form {form}")
        columns.append({"name": name, "offset": offset, "repeat": repeat, "format": fmt})
        offset += size
    return columns


def read_binary_table(data: bytes, hdu: dict[str, object]) -> list[dict[str, float | int]]:
    header = hdu["header"]
    row_size = int(header["NAXIS1"])
    row_count = int(header["NAXIS2"])
    start = int(hdu["data_start"])
    columns = table_columns(header)
    rows = []
    for row_index in range(row_count):
        row_start = start + row_index * row_size
        row: dict[str, float | int] = {}
        for column in columns:
            values = struct.unpack(
                str(column["format"]),
                data[row_start + int(column["offset"]) : row_start + int(column["offset"]) + struct.calcsize(str(column["format"]))],
            )
            value = values[0] if int(column["repeat"]) == 1 else values
            row[str(column["name"])] = value
        rows.append(row)
    return rows


def cosebis_fits_bytes(tarball: Path = RAW_TARBALL) -> bytes:
    fetch_tarball(tarball)
    with tarfile.open(tarball, "r:gz") as archive:
        for name in archive.getnames():
            if "/data_fits/cosebis_" in name and name.endswith(".fits"):
                member = archive.extractfile(name)
                if member is None:
                    break
                return member.read()
    raise FileNotFoundError("cosebis FITS product not found")


def build_cosebis_contract(data: bytes | None = None) -> dict:
    fits = data if data is not None else cosebis_fits_bytes()
    hdus = read_fits_hdus(fits)
    covariance = read_image_float64(fits, find_hdu(hdus, "COVMAT"))
    observed_rows = read_binary_table(fits, find_hdu(hdus, "En"))
    nz_rows = read_binary_table(fits, find_hdu(hdus, "NZ_SOURCE"))
    observed = [float(row["VALUE"]) for row in observed_rows]
    z = [float(row["Z_MID"]) for row in nz_rows]
    weights = [sum(float(row[f"BIN{index}"]) for index in range(1, 6)) for row in nz_rows]
    z_min = min(float(row["Z_LOW"]) for row in nz_rows)
    z_max = max(float(row["Z_HIGH"]) for row in nz_rows)
    return {
        "survey_id": "KiDS-1000",
        "observable_name": "COSEBIs cosmic shear En",
        "n_z": {"z": z, "weights": weights},
        "tomographic_bins": [{"z_min": z_min, "z_max": z_max, "source": "combined NZ_SOURCE bins"}],
        "observed_vector": observed,
        "prediction_vector_id": "janus-kids1000-cosebis-fixed-prediction-pending",
        "covariance": covariance,
        "mask_window": {"description": "KiDS-1000 public COSEBIs FITS product window/mask encoded by supplied En statistic"},
        "nuisance_parameters_declared": [],
        "n_fit_parameters": 0,
    }


def build_payload() -> dict:
    contract = build_cosebis_contract()
    contract_payload = build_contract_payload(contract)
    return {
        "description": "KiDS-1000 COSEBIs survey contract extracted from the official public FITS product.",
        "status": "kids1000-cosebis-contract-ready",
        "contract": contract,
        "validation": contract_payload["validation"],
        "survey_layer_ready": contract_payload["survey_layer_ready"],
        "boundary": (
            "Structural contract only. A Janus prediction vector with the same En ordering "
            "is still required before computing chi-square."
        ),
    }


def render_markdown(payload: dict) -> str:
    contract = payload["contract"]
    covariance = contract["covariance"]
    observed = contract["observed_vector"]
    nz = contract["n_z"]
    lines = [
        "# KiDS-1000 COSEBIs Contract",
        "",
        payload["description"],
        "",
        f"Status: `{payload['status']}`",
        f"Survey layer ready: `{payload['survey_layer_ready']}`",
        f"Observed vector dimension: `{len(observed)}`",
        f"Covariance shape: `{len(covariance)} x {len(covariance[0])}`",
        f"n(z) points: `{len(nz['z'])}`",
        f"Validation errors: `{payload['validation']['errors']}`",
        "",
        payload["boundary"],
        "",
    ]
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
