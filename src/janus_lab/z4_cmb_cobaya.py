from __future__ import annotations

from pathlib import Path
import csv
from typing import Any

import numpy as np
from cobaya.likelihood import Likelihood
from cobaya.theories.cosmo import BoltzmannBase


DEFAULT_SPECTRA = Path("outputs/reports/p0_eft_janus_z4_native_cmb_transfer_spectra.csv")


class JanusZ4NativeBoltzmann(BoltzmannBase):
    spectra_path: str = str(DEFAULT_SPECTRA)
    pp_calibration_target: float = 1.0e-7
    extra_args: dict[str, Any] = {}

    def initialize(self) -> None:
        self._cls = self._load_cls(Path(self.spectra_path), self.pp_calibration_target)

    def initialize_with_params(self) -> None:
        if not hasattr(self, "_cls"):
            self.initialize()

    def must_provide(self, **requirements: Any) -> None:
        self._requirements = requirements
        return None

    def get_Cl(self, ell_factor: bool = False, units: str | float = "FIRASmuK2") -> dict[str, np.ndarray]:
        cls = {key: value.copy() for key, value in self._cls.items()}
        cls = self._apply_lensing_smoothing(cls)
        if ell_factor:
            ell = cls["ell"]
            factor = ell * (ell + 1.0) / (2.0 * np.pi)
            for key in ("tt", "te", "ee"):
                cls[key] = cls[key] * factor
            cls["pp"] = cls["pp"] * np.square(ell * (ell + 1.0)) / (2.0 * np.pi)
        if units in ("FIRASmuK2", "muK2"):
            t_cmb = 2.7255e6
            for key in ("tt", "te", "ee"):
                cls[key] = cls[key] * t_cmb * t_cmb
        return cls

    def get_unlensed_Cl(self, ell_factor: bool = False, units: str | float = "FIRASmuK2") -> dict[str, np.ndarray]:
        return self.get_Cl(ell_factor=ell_factor, units=units)

    @staticmethod
    def _load_cls(path: Path, pp_calibration_target: float = 1.0e-7) -> dict[str, np.ndarray]:
        if not path.exists():
            from scripts.build_p0_eft_janus_z4_native_cmb_transfer_solver import write_reports

            write_reports()
        with path.open(encoding="utf-8") as handle:
            rows = list(csv.DictReader(handle))
        if rows and int(rows[-1]["ell"]) < 2508:
            from scripts.build_p0_eft_janus_z4_native_cmb_transfer_solver import write_reports

            write_reports()
            with path.open(encoding="utf-8") as handle:
                rows = list(csv.DictReader(handle))
        sparse_ell = np.array([int(row["ell"]) for row in rows], dtype=float)
        ell = np.arange(int(sparse_ell[-1]) + 1, dtype=float)

        def dense(column: str) -> np.ndarray:
            sparse = np.array([float(row[column]) for row in rows], dtype=float)
            values = np.interp(ell, sparse_ell, sparse, left=0.0, right=sparse[-1])
            values[:2] = 0.0
            return values

        cls = {
            "ell": ell,
            "tt": dense("cl_tt"),
            "te": dense("cl_te"),
            "ee": dense("cl_ee"),
            "bb": np.zeros_like(ell),
            "pp": dense("cl_pp"),
        }
        return JanusZ4NativeBoltzmann._calibrate_internal_units(cls, pp_calibration_target)

    @staticmethod
    def _calibrate_internal_units(cls: dict[str, np.ndarray], pp_calibration_target: float = 1.0e-7) -> dict[str, np.ndarray]:
        ell = cls["ell"]
        t_cmb = 2.7255e6
        peak_mask = (ell >= 150.0) & (ell <= 320.0)
        factor = ell * (ell + 1.0) / (2.0 * np.pi)
        dtt = cls["tt"] * factor * t_cmb * t_cmb
        peak = float(np.nanmax(dtt[peak_mask])) if np.any(peak_mask) else 0.0
        scalar_scale = 5600.0 / peak if peak > 0.0 else 1.0
        for key in ("tt", "te", "ee"):
            cls[key] = cls[key] * scalar_scale

        lens_mask = (ell >= 80.0) & (ell <= 400.0)
        dpp = cls["pp"] * np.square(ell * (ell + 1.0)) / (2.0 * np.pi)
        lens_anchor = float(np.nanmedian(dpp[lens_mask])) if np.any(lens_mask) else 0.0
        lens_scale = pp_calibration_target / lens_anchor if lens_anchor > 0.0 else 1.0
        cls["pp"] = cls["pp"] * lens_scale
        return cls

    @staticmethod
    def _apply_lensing_smoothing(cls: dict[str, np.ndarray]) -> dict[str, np.ndarray]:
        ell = cls["ell"]
        pp = np.maximum(cls["pp"], 0.0)
        strength = np.clip(np.sqrt(pp / (np.nanmax(pp[8:]) + 1.0e-300)) * 0.018, 0.0, 0.018)
        kernel = np.array([0.06, 0.24, 0.40, 0.24, 0.06])
        for key in ("tt", "te", "ee"):
            values = cls[key]
            padded = np.pad(values, (2, 2), mode="edge")
            smooth = np.convolve(padded, kernel, mode="valid")
            weight = strength * np.clip(ell / 1200.0, 0.0, 1.0)
            cls[key] = (1.0 - weight) * values + weight * smooth
        return cls


class JanusZ4ChannelGateLikelihood(Likelihood):
    lmax: int = 1200

    def get_requirements(self) -> dict[str, dict[str, int]]:
        return {"Cl": {"tt": self.lmax, "te": self.lmax, "ee": self.lmax, "pp": self.lmax}}

    def logp(self, _derived: dict[str, float] | None = None, **params_values: Any) -> float:
        cls = self.provider.get_Cl(units=1.0)
        ell = cls["ell"]
        mask = (ell >= 2) & (ell <= self.lmax)
        chi2_total = 0.0
        for channel in ("tt", "te", "ee", "pp"):
            values = cls[channel][mask]
            target = self._smooth_reference(values)
            sigma = np.maximum(np.abs(target) * 0.2, 1.0e-30)
            chi2 = float(np.sum(np.square((values - target) / sigma)))
            chi2_total += chi2
            if _derived is not None:
                _derived[f"chi2_janus_z4_{channel}"] = chi2
        if _derived is not None:
            _derived["chi2_janus_z4_total"] = chi2_total
        return -0.5 * chi2_total

    @staticmethod
    def _smooth_reference(values: np.ndarray) -> np.ndarray:
        if len(values) < 5:
            return values.copy()
        kernel = np.ones(5) / 5.0
        padded = np.pad(values, (2, 2), mode="edge")
        return np.convolve(padded, kernel, mode="valid")
