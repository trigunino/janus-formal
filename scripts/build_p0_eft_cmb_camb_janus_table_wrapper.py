from __future__ import annotations

from pathlib import Path
import csv
import json
import math

try:
    from scripts.build_p0_eft_cmb_camb_backend_smoke import build_payload as camb_payload
except ModuleNotFoundError:
    from build_p0_eft_cmb_camb_backend_smoke import build_payload as camb_payload

REPORT_PATH = Path("outputs/reports/p0_eft_cmb_camb_janus_table_wrapper.md")
JSON_PATH = Path("outputs/reports/p0_eft_cmb_camb_janus_table_wrapper.json")
CSV_PATH = Path("outputs/cmb_bridge/camb_janus_table_wrapped_cls.csv")
MANIFEST_PATH = Path("outputs/cmb_bridge/manifest.json")


def read_dict_rows(path: Path) -> list[dict[str, float]]:
    with path.open(newline="", encoding="utf-8") as handle:
        return [{k: float(v) for k, v in row.items()} for row in csv.DictReader(handle)]


def load_manifest() -> dict:
    return json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))


def late_lensing_weight(a: float) -> float:
    return math.exp(-0.5 * ((a - 0.667) / 0.22) ** 2)


def sigma_by_k(mu_sigma_rows: list[dict[str, float]]) -> dict[float, float]:
    grouped: dict[float, list[tuple[float, float]]] = {}
    for row in mu_sigma_rows:
        grouped.setdefault(row["k"], []).append((row["a"], row["Sigma_JH"]))
    out: dict[float, float] = {}
    for k, values in grouped.items():
        weights = [late_lensing_weight(a) for a, _ in values]
        norm = sum(weights)
        out[k] = sum(w * sigma for w, (_, sigma) in zip(weights, values)) / norm
    return out


def interp_log_k(table: dict[float, float], k_eff: float) -> float:
    keys = sorted(table)
    if k_eff <= keys[0]:
        return table[keys[0]]
    if k_eff >= keys[-1]:
        return table[keys[-1]]
    log_k = math.log(k_eff)
    for lo, hi in zip(keys, keys[1:]):
        if lo <= k_eff <= hi:
            t = (log_k - math.log(lo)) / (math.log(hi) - math.log(lo))
            return table[lo] * (1.0 - t) + table[hi] * t
    return table[keys[-1]]


def ell_to_k(ell: int, k_min: float, k_max: float, lmax: int) -> float:
    if ell <= 2:
        return k_min
    t = math.log(ell / 2.0) / math.log(max(lmax / 2.0, 2.0))
    return math.exp(math.log(k_min) * (1.0 - t) + math.log(k_max) * t)


def write_wrapped_cls(camb_cls_path: Path, sigma_table: dict[float, float], lmax: int) -> dict:
    k_min, k_max = min(sigma_table), max(sigma_table)
    rows = read_dict_rows(camb_cls_path)
    CSV_PATH.parent.mkdir(parents=True, exist_ok=True)
    max_abs_fractional_shift = 0.0
    with CSV_PATH.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.writer(handle)
        writer.writerow(["ell", "TT", "EE", "BB", "TE", "k_eff", "Sigma_eff", "wrapper_factor"])
        for row in rows:
            ell = int(row["ell"])
            k_eff = ell_to_k(ell, k_min, k_max, lmax)
            sigma_eff = interp_log_k(sigma_table, k_eff)
            lensing_scale = ell / (ell + 250.0) if ell > 1 else 0.0
            wrapper_factor = 1.0 + 0.20 * (sigma_eff - 1.0) * lensing_scale
            max_abs_fractional_shift = max(max_abs_fractional_shift, abs(wrapper_factor - 1.0))
            writer.writerow(
                [
                    ell,
                    row["TT"] * wrapper_factor,
                    row["EE"] * wrapper_factor,
                    row["BB"] * wrapper_factor,
                    row["TE"] * wrapper_factor,
                    k_eff,
                    sigma_eff,
                    wrapper_factor,
                ]
            )
    return {
        "wrapped_cls_csv": str(CSV_PATH),
        "k_min": k_min,
        "k_max": k_max,
        "max_abs_fractional_shift": max_abs_fractional_shift,
    }


def build_payload(lmax: int = 800) -> dict:
    camb = camb_payload(lmax=lmax)
    manifest = load_manifest()
    mu_sigma_path = Path(manifest["files"]["modified_gravity"])
    mu_sigma_rows = read_dict_rows(mu_sigma_path)
    sigma_table = sigma_by_k(mu_sigma_rows)
    wrapper = write_wrapped_cls(Path(camb["camb_run"]["cls_csv"]), sigma_table, lmax)
    payload = {
        "description": "CAMB wrapper pass consuming Janus-Holst tabulated mu/Sigma data after the stock CAMB solve.",
        "status": "camb-janus-table-wrapper-run",
        "backend_solver_run": camb["backend_solver_run"],
        "stock_camb_used": True,
        "janus_modified_gravity_tables_consumed": True,
        "exact_camb_fork": False,
        "boltzmann_equations_modified_in_solver": False,
        "post_camb_weyl_lensing_wrapper": True,
        "uncompressed_planck_likelihood_used": False,
        "direct_cmb_likelihood_ready": False,
        "modified_gravity_table": str(mu_sigma_path),
        "wrapper": wrapper,
        "next_required": (
            "Promote this post-CAMB wrapper into a true CAMB fork/source-evolution patch before using it as a direct CMB likelihood."
        ),
    }
    return payload


def render_markdown(payload: dict) -> str:
    wrapper = payload["wrapper"]
    return "\n".join(
        [
            "# P0 EFT CMB CAMB Janus Table Wrapper",
            "",
            payload["description"],
            "",
            f"Status: {payload['status']}",
            f"Backend solver run: {payload['backend_solver_run']}",
            f"Janus modified-gravity tables consumed: {payload['janus_modified_gravity_tables_consumed']}",
            f"Exact CAMB fork: {payload['exact_camb_fork']}",
            f"Boltzmann equations modified in solver: {payload['boltzmann_equations_modified_in_solver']}",
            f"Post-CAMB Weyl/lensing wrapper: {payload['post_camb_weyl_lensing_wrapper']}",
            f"Direct CMB likelihood ready: {payload['direct_cmb_likelihood_ready']}",
            "",
            "## Output",
            "",
            f"- wrapped spectra: `{wrapper['wrapped_cls_csv']}`",
            f"- k range: `{wrapper['k_min']}` to `{wrapper['k_max']}`",
            f"- max fractional shift: `{wrapper['max_abs_fractional_shift']}`",
            "",
            "## Next",
            "",
            payload["next_required"],
            "",
        ]
    )


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH, lmax: int = 800) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload(lmax=lmax)
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")
    print(f"Wrote {CSV_PATH}")


if __name__ == "__main__":
    main()
