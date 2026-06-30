from __future__ import annotations

import csv
from pathlib import Path

import numpy as np

from janus_lab.bao_maps import power_law_scale, sqrt_a_scale


REQUIRED_RULER_CSV = Path("outputs/reports/janus_bao_required_ruler.csv")
REPORT_PATH = Path("outputs/reports/janus_bao_observable_map_v1.md")


def load_required_rows() -> list[dict[str, str]]:
    if not REQUIRED_RULER_CSV.exists():
        raise FileNotFoundError(
            f"Missing {REQUIRED_RULER_CSV}. Run scripts/infer_janus_bao_ruler.py first."
        )
    with REQUIRED_RULER_CSV.open(encoding="utf-8") as handle:
        return list(csv.DictReader(handle))


def fit_power(rows: list[dict[str, str]], quantity: str) -> tuple[int, float | None, float | None]:
    selected = [row for row in rows if row["quantity"] == quantity]
    if len(selected) < 2:
        return len(selected), None, None
    x = np.asarray([np.log1p(float(row["z"])) for row in selected])
    y = np.asarray([np.log(float(row["effective_scale"])) for row in selected])
    design = np.column_stack([np.ones_like(x), x])
    coeffs, *_ = np.linalg.lstsq(design, y, rcond=None)
    return len(selected), float(np.exp(coeffs[0])), float(coeffs[1])


def rms_against_sqrt_a(rows: list[dict[str, str]], quantity: str) -> tuple[int, float, float]:
    selected = [row for row in rows if row["quantity"] == quantity]
    z = np.asarray([float(row["z"]) for row in selected])
    scale = np.asarray([float(row["effective_scale"]) for row in selected])
    template = np.asarray(sqrt_a_scale(z, amplitude=1.0))
    amplitude = float(np.dot(template, scale) / np.dot(template, template))
    residual = scale - amplitude * template
    return len(selected), amplitude, float(np.sqrt(np.mean(residual**2)))


def main() -> None:
    rows = load_required_rows()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)

    power_lines: list[str] = []
    sqrt_lines: list[str] = []
    for quantity in ["DM_over_rs", "DH_over_rs", "DV_over_rs"]:
        n_rows, amplitude, power = fit_power(rows, quantity)
        if amplitude is None or power is None:
            power_lines.append(f"| {quantity} | {n_rows} | underconstrained | underconstrained |")
        else:
            power_lines.append(f"| {quantity} | {n_rows} | {amplitude:.6g} | {power:.6g} |")
        sqrt_n, sqrt_amp, sqrt_rms = rms_against_sqrt_a(rows, quantity)
        status = "underconstrained" if sqrt_n < 2 else "fit"
        sqrt_lines.append(f"| {quantity} | {sqrt_n} | {sqrt_amp:.6g} | {sqrt_rms:.6g} | {status} |")

    lines = [
        "# Janus BAO Observable Map v1",
        "",
        "This report connects the formal BAO map draft to the current DESI residual inversion.",
        "",
        "Formal draft: `formal/axioms/bao_observable_map.md`.",
        "Input residual inversion: `outputs/reports/janus_bao_required_ruler.csv`.",
        "C2 constrained score: `outputs/reports/janus_bao_c2_gauge_score.md`.",
        "C4 observable-map score: `outputs/reports/janus_bao_c4_observable_score.md`.",
        "C5 redshift-map score: `outputs/reports/janus_bao_c5_redshift_score.md`.",
        "C6 sound-horizon score: `outputs/reports/janus_bao_c6_sound_horizon_score.md`.",
        "C7 anisotropic-linear score: `outputs/reports/janus_bao_c7_anisotropic_linear_ruler_score.md`.",
        "C8 source-gauge no-fit score: `outputs/reports/janus_bao_c8_source_gauge_no_fit_score.md`.",
        "",
        "Rule: C3/C7-style fitted shapes are diagnostics only. Evidence requires a source-derived shape fixed before comparison to data.",
        "",
        "## Candidate Maps",
        "",
        "| ID | Formula | Status |",
        "|---|---|---|",
        "| C0 | `S_Q(z)=S0` | baseline; too rigid |",
        "| C1 | `S_Q(z)=S0/sqrt(1+z)` | source-motivated by Eq. 40; insufficient alone |",
        "| C2 | `S_DM=A_DM f_DM(a)`, `S_DH=A_DH f_DH(a)` | main derivation target |",
        "| C3 | `S_Q(z)=A_Q+B_Q z` | empirical inverse map only |",
        "| C4 | gauge-modified `D_M`, `D_H` | insufficient; prefers `q0` close to zero |",
        "| C5 | `1+z_geom=(1+z_obs)^gamma` | rejected as main fix |",
        "| C6 | `S(z)=A(1+z)^p` | common ruler evolution insufficient |",
        "| C7 | linear `S_DM`, `S_DH`; derived `S_DV` | best diagnostic target; not admissible evidence |",
        "| C8 | source-fixed gauge powers, `q0=-0.087` | no-fit admissible test; still insufficient |",
        "",
        "## Inferred Power-Law Summary",
        "",
        "Fit form: `S_Q(z) ~= A_Q * (1+z)^p_Q`.",
        "",
        "| quantity | n | A | p |",
        "|---|---:|---:|---:|",
        *power_lines,
        "",
        "## Distance From Pure sqrt(a)",
        "",
        "Fit form: `S_Q(z) ~= A_Q / sqrt(1+z)`.",
        "",
        "| quantity | n | best A | RMS residual | status |",
        "|---|---:|---:|---:|---|",
        *sqrt_lines,
        "",
        "## Interpretation",
        "",
        "- `DM_over_rs` and `DH_over_rs` prefer powers close to `-1/2`, matching the variable-constants clue.",
        "- `DV_over_rs` is less stable because it mixes transverse/radial information and has fewer independent rows.",
        "- Pure `sqrt(a)` is too constrained; the next derivation must explain both the near-`sqrt(a)` trend and the quantity-dependent offsets.",
        "- The constrained C2/C2b score shows that an effective-ruler multiplier alone is likely insufficient.",
        "- C4 improves slightly over C2b but still prefers `q0` close to zero, so a simple gauge-power observable map is insufficient.",
        "- C5 is worse than C4 and keeps `gamma` close to 1, so redshift remapping alone is not the missing ingredient.",
        "- C6 shows that a constant `r_d` is only the fitted global scale, and a common evolving ruler is still insufficient.",
        "- C7 is the current best diagnostic target: anisotropic linear rulers with derived `D_V` beat C4/C5/C6 and keep `q0=-0.087` competitive, but this is not evidence until derived.",
        "- C8 applies the anti-fit rule. Direct source-gauge laws from M18/X2026 do not yet solve DESI BAO.",
        "",
        "## Next Derivation Step",
        "",
        "Derive or reject the C7 anisotropy from source equations. No additional fitted shape should be promoted unless its form is fixed before the data test.",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")

    # Touch the helpers so this script fails if candidate-map API drifts.
    _ = power_law_scale(np.asarray([0.5]), 1.0, -0.5)

    print(f"Wrote {REPORT_PATH}")


if __name__ == "__main__":
    main()
