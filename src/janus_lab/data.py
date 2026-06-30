"""Load and download observational datasets used by Janus Lab."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from urllib.request import Request, urlopen

import numpy as np


DATA_URLS = {
    "desi_dr2_bao_mean": "https://raw.githubusercontent.com/CobayaSampler/bao_data/master/desi_bao_dr2/desi_gaussian_bao_ALL_GCcomb_mean.txt",
    "desi_dr2_bao_cov": "https://raw.githubusercontent.com/CobayaSampler/bao_data/master/desi_bao_dr2/desi_gaussian_bao_ALL_GCcomb_cov.txt",
    "pantheon_shoes": "https://github.com/PantheonPlusSH0ES/DataRelease/raw/refs/heads/main/Pantheon+_Data/4_DISTANCES_AND_COVAR/Pantheon+SH0ES.dat",
    "pantheon_shoes_cov": "https://github.com/PantheonPlusSH0ES/DataRelease/raw/refs/heads/main/Pantheon+_Data/4_DISTANCES_AND_COVAR/Pantheon+SH0ES_STAT+SYS.cov",
}


DATA_FILES = {
    "desi_dr2_bao_mean": Path("data/raw/desi_dr2/desi_gaussian_bao_ALL_GCcomb_mean.txt"),
    "desi_dr2_bao_cov": Path("data/raw/desi_dr2/desi_gaussian_bao_ALL_GCcomb_cov.txt"),
    "pantheon_shoes": Path("data/raw/pantheon_plus/Pantheon+SH0ES.dat"),
    "pantheon_shoes_cov": Path("data/raw/pantheon_plus/Pantheon+SH0ES_STAT+SYS.cov"),
}


@dataclass(frozen=True)
class BaoDataset:
    z: np.ndarray
    value: np.ndarray
    quantity: np.ndarray
    covariance: np.ndarray


@dataclass(frozen=True)
class PantheonDataset:
    z: np.ndarray
    mu: np.ndarray
    sigma_mu: np.ndarray


def download_file(url: str, destination: Path, force: bool = False) -> Path:
    """Download a URL to ``destination`` if missing."""

    destination = Path(destination)
    if destination.exists() and not force:
        return destination

    destination.parent.mkdir(parents=True, exist_ok=True)
    request = Request(url, headers={"User-Agent": "janus-lab/0.1"})
    with urlopen(request, timeout=120) as response:
        data = response.read()
    destination.write_bytes(data)
    return destination


def ensure_default_data(force: bool = False) -> dict[str, Path]:
    """Download the default public datasets used by the first experiments."""

    downloaded: dict[str, Path] = {}
    for key, url in DATA_URLS.items():
        downloaded[key] = download_file(url, DATA_FILES[key], force=force)
    return downloaded


def load_desi_bao(
    mean_path: Path = DATA_FILES["desi_dr2_bao_mean"],
    cov_path: Path = DATA_FILES["desi_dr2_bao_cov"],
) -> BaoDataset:
    """Load DESI DR2 BAO mean vector and covariance from Cobaya files."""

    rows: list[tuple[float, float, str]] = []
    for raw_line in Path(mean_path).read_text(encoding="utf-8").splitlines():
        line = raw_line.strip()
        if not line or line.startswith("#"):
            continue
        parts = line.split()
        rows.append((float(parts[0]), float(parts[1]), parts[2]))

    if not rows:
        raise ValueError(f"No DESI BAO rows found in {mean_path}")

    z = np.asarray([row[0] for row in rows], dtype=float)
    value = np.asarray([row[1] for row in rows], dtype=float)
    quantity = np.asarray([row[2] for row in rows], dtype=str)

    cov_values = np.loadtxt(cov_path, dtype=float)
    cov_values = np.ravel(cov_values)
    size = int(np.sqrt(cov_values.size))
    if size * size != cov_values.size:
        raise ValueError(f"Covariance length is not square: {cov_values.size}")
    covariance = cov_values.reshape(size, size)
    if covariance.shape != (len(rows), len(rows)):
        raise ValueError(
            f"Covariance shape {covariance.shape} does not match {len(rows)} rows"
        )

    return BaoDataset(z=z, value=value, quantity=quantity, covariance=covariance)


def load_pantheon_diag(path: Path = DATA_FILES["pantheon_shoes"]) -> PantheonDataset:
    """Load Pantheon+SH0ES redshift, distance modulus and diagonal errors.

    This is an exploratory loader. Production fits should use the full covariance
    after deciding whether the SH0ES Cepheid-host covariance is included.
    """

    header = Path(path).read_text(encoding="utf-8").splitlines()[0].split()
    required = ["zHD", "MU_SH0ES", "MU_SH0ES_ERR_DIAG"]
    indices = [header.index(name) for name in required]
    data = np.genfromtxt(path, names=True, usecols=indices, dtype=float)
    return PantheonDataset(
        z=np.asarray(data["zHD"], dtype=float),
        mu=np.asarray(data["MU_SH0ES"], dtype=float),
        sigma_mu=np.asarray(data["MU_SH0ES_ERR_DIAG"], dtype=float),
    )
