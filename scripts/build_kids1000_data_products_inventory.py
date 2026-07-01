from __future__ import annotations

from pathlib import Path
import json
import math
import tarfile
import urllib.request


PRODUCTS_URL = "https://kids.strw.leidenuniv.nl/DR4/data_files/KiDS1000_cosmic_shear_data_release.tgz"
RAW_DIR = Path("data/raw/kids1000")
RAW_TARBALL = RAW_DIR / "KiDS1000_cosmic_shear_data_release.tgz"
REPORT_PATH = Path("outputs/reports/kids1000_data_products_inventory.md")
JSON_PATH = Path("outputs/reports/kids1000_data_products_inventory.json")

USABLE_PRODUCTS = {
    "cosebis": {
        "fits_prefix": "cosebis_",
        "data_vector_extensions": ["En"],
        "covariance_extension": "COVMAT",
        "redshift_extensions": [],
        "role": "fiducial KiDS-1000 cosmic-shear statistic",
    },
    "xipm": {
        "fits_prefix": "xipm_",
        "data_vector_extensions": ["xip", "xim"],
        "covariance_extension": "COVMAT",
        "redshift_extensions": [],
        "role": "two-point shear correlation cross-check",
    },
    "bp": {
        "fits_prefix": "bp_",
        "data_vector_extensions": ["PeeE"],
        "covariance_extension": "COVMAT",
        "redshift_extensions": ["nz_source"],
        "role": "band-power cross-check with source n(z)",
    },
}


def fetch_tarball(path: Path = RAW_TARBALL) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    if not path.exists():
        urllib.request.urlretrieve(PRODUCTS_URL, path)
    return path


def classify_member(name: str) -> str:
    lower = name.lower()
    filename = Path(lower).name
    if filename.startswith("._") or filename == ".ds_store":
        return "macos_metadata"
    if lower.endswith((".py", ".ipynb")):
        return "analysis_script"
    if lower.endswith((".fits", ".fit", ".fits.gz")):
        return "fits_data_product"
    if lower.endswith((".ini", ".yaml", ".yml")):
        return "pipeline_config"
    if "/chain/" in lower and lower.endswith(".txt"):
        return "posterior_chain"
    if lower.endswith((".txt", ".dat", ".asc")) and "cov" in filename:
        return "covariance_text"
    if "multinest" in filename or lower.endswith(".paramnames"):
        return "posterior_chain"
    if "nofz" in lower or "n_z" in lower or "redshift" in lower:
        return "redshift_distribution"
    return "other"


def inventory_tarball(path: Path) -> list[dict[str, object]]:
    with tarfile.open(path, "r:gz") as archive:
        rows = []
        for member in archive.getmembers():
            if member.isdir():
                continue
            rows.append(
                {
                    "name": member.name,
                    "size": member.size,
                    "kind": classify_member(member.name),
                }
            )
    return sorted(rows, key=lambda row: str(row["name"]))


def summarize(rows: list[dict[str, object]]) -> dict[str, int]:
    summary: dict[str, int] = {}
    for row in rows:
        kind = str(row["kind"])
        summary[kind] = summary.get(kind, 0) + 1
    return dict(sorted(summary.items()))


def parse_fits_value(raw: str) -> object:
    value = raw.split("/", 1)[0].strip()
    if not value:
        return ""
    if value.startswith("'") and "'" in value[1:]:
        return value[1:].split("'", 1)[0].strip()
    if value in {"T", "F"}:
        return value == "T"
    try:
        return int(value)
    except ValueError:
        try:
            return float(value.replace("D", "E"))
        except ValueError:
            return value


def parse_fits_headers(data: bytes) -> list[dict[str, object]]:
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
        offset += header_size
        naxis = int(header.get("NAXIS", 0) or 0)
        bitpix = abs(int(header.get("BITPIX", 8) or 8))
        pcount = int(header.get("PCOUNT", 0) or 0)
        gcount = int(header.get("GCOUNT", 1) or 1)
        data_units = 0 if naxis == 0 else 1
        for axis in range(1, naxis + 1):
            data_units *= int(header.get(f"NAXIS{axis}", 0) or 0)
        data_size = ((bitpix // 8) * data_units + pcount) * gcount
        offset += int(math.ceil(data_size / 2880) * 2880) if data_size else 0
        ttypes = [
            str(header[key])
            for key in sorted(header)
            if key.startswith("TTYPE") and str(header[key]).strip()
        ]
        hdus.append(
            {
                "extname": str(header.get("EXTNAME", "PRIMARY")),
                "xtension": str(header.get("XTENSION", "PRIMARY")),
                "naxis1": int(header.get("NAXIS1", 0) or 0),
                "naxis2": int(header.get("NAXIS2", 0) or 0),
                "tfields": int(header.get("TFIELDS", 0) or 0),
                "columns": ttypes,
            }
        )
        if offset >= len(data):
            break
    return hdus


def fits_headers_from_tarball(path: Path, rows: list[dict[str, object]]) -> dict[str, list[dict[str, object]]]:
    fits_rows = [row for row in rows if row["kind"] == "fits_data_product"]
    with tarfile.open(path, "r:gz") as archive:
        headers = {}
        for row in fits_rows:
            member = archive.extractfile(str(row["name"]))
            if member is None:
                continue
            headers[str(row["name"])] = parse_fits_headers(member.read())
    return headers


def build_payload(fetch: bool = True) -> dict:
    tarball = fetch_tarball() if fetch else RAW_TARBALL
    rows = inventory_tarball(tarball)
    fits_headers = fits_headers_from_tarball(tarball, rows)
    return {
        "description": "Inventory of official KiDS-1000 cosmic-shear public data products.",
        "status": "kids1000-data-products-inventoried",
        "source_url": PRODUCTS_URL,
        "raw_tarball": str(tarball),
        "file_count": len(rows),
        "kind_counts": summarize(rows),
        "usable_products": USABLE_PRODUCTS,
        "fits_headers": fits_headers,
        "rows": rows,
        "next_required": [
            "use the COSEBIs contract as the fiducial KiDS hard-test surface",
            "map xipm and band-power products only as cross-check surfaces",
            "compute a Janus prediction vector in the same En ordering before chi-square",
        ],
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# KiDS-1000 Data Products Inventory",
        "",
        payload["description"],
        "",
        f"Status: `{payload['status']}`",
        f"Source URL: {payload['source_url']}",
        f"Raw tarball: `{payload['raw_tarball']}`",
        f"File count: `{payload['file_count']}`",
        "",
        "## Kind Counts",
        "",
        "| kind | count |",
        "|---|---:|",
    ]
    for kind, count in payload["kind_counts"].items():
        lines.append(f"| {kind} | {count} |")
    lines.extend(
        [
            "",
            "## FITS Extension Map",
            "",
            "| statistic | role | data vectors | covariance | n(z) |",
            "|---|---|---|---|---|",
        ]
    )
    for name, product in payload["usable_products"].items():
        lines.append(
            f"| {name} | {product['role']} | "
            f"{', '.join(product['data_vector_extensions'])} | "
            f"{product['covariance_extension']} | "
            f"{', '.join(product['redshift_extensions']) or 'not in reader example'} |"
        )
    lines.extend(["", "## FITS HDUs", "", "| file | extension | rows | columns |", "|---|---|---:|---|"])
    for filename, hdus in payload["fits_headers"].items():
        short = Path(filename).name
        for hdu in hdus:
            columns = ", ".join(hdu["columns"][:6])
            if len(hdu["columns"]) > 6:
                columns += ", ..."
            lines.append(f"| `{short}` | {hdu['extname']} | {hdu['naxis2']} | {columns} |")
    lines.extend(["", "## First Files", "", "| kind | size | name |", "|---|---:|---|"])
    for row in payload["rows"][:40]:
        lines.append(f"| {row['kind']} | {row['size']} | `{row['name']}` |")
    lines.extend(["", "## Next Required"])
    lines.extend(f"- {item}" for item in payload["next_required"])
    lines.append("")
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
