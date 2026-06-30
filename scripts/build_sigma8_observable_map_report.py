from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/sigma8_observable_map.md")
MAP_PATH = Path("formal/axioms/sigma8_observable_map.md")
GAUSSIAN_PATH = Path("outputs/reports/sigma8_normalized_ic_3d.json")
LOGNORMAL_PATH = Path("outputs/reports/lognormal_sigma8_ic_3d.json")
BOUNDED_PATH = Path("outputs/reports/bounded_anticorrelated_sigma8_ic_3d.json")
LENSING_PATH = Path("outputs/reports/lensing_sigma8_observable.json")
PROJECTION_PATH = Path("outputs/reports/weak_lensing_projection.json")
JANUS_KERNEL_PATH = Path("outputs/reports/janus_tomographic_lensing_kernel.json")
SHEAR_PATH = Path("outputs/reports/janus_shear_proxy.json")
SOURCE_DISTRIBUTION_PATH = Path("outputs/reports/janus_source_distribution_lensing.json")
ABSOLUTE_CONVERGENCE_PATH = Path("outputs/reports/janus_absolute_convergence.json")
LENSING_AUDIT_PATH = Path("outputs/reports/lensing_normalization_audit.json")


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    gaussian = load_json(GAUSSIAN_PATH)
    lognormal = load_json(LOGNORMAL_PATH)
    bounded = load_json(BOUNDED_PATH)
    lensing = load_json(LENSING_PATH) if LENSING_PATH.exists() else None
    projection = load_json(PROJECTION_PATH) if PROJECTION_PATH.exists() else None
    janus_kernel = load_json(JANUS_KERNEL_PATH) if JANUS_KERNEL_PATH.exists() else None
    shear = load_json(SHEAR_PATH) if SHEAR_PATH.exists() else None
    source_distribution = (
        load_json(SOURCE_DISTRIBUTION_PATH) if SOURCE_DISTRIBUTION_PATH.exists() else None
    )
    absolute_convergence = (
        load_json(ABSOLUTE_CONVERGENCE_PATH) if ABSOLUTE_CONVERGENCE_PATH.exists() else None
    )
    lensing_audit = load_json(LENSING_AUDIT_PATH) if LENSING_AUDIT_PATH.exists() else None
    map_text = MAP_PATH.read_text(encoding="utf-8")

    lines = [
        "# Sigma8 Observable Map Report",
        "",
        "Reproducible summary of the current Janus `sigma8` observable status.",
        "",
        "## Numerical Constraints",
        "",
        "| IC family | target sigma8 | achieved/capacity | density safe | sector correlation | reading |",
        "|---|---:|---:|---|---:|---|",
        (
            f"| Gaussian direct | {gaussian['target_sigma8']:.6g} | "
            f"{gaussian['achieved_sigma8']:.6g} | "
            f"{gaussian['density_contrast_safe']} | n/a | reaches target but violates `delta > -1` |"
        ),
        (
            f"| Lognormal | {lognormal['target_sigma8']:.6g} | "
            f"{lognormal['positive_sigma8']:.6g} | "
            f"{lognormal['positive_density_safe'] and lognormal['negative_density_safe']} | "
            f"{lognormal['sector_correlation']:.6g} | density-safe but weak sector anti-correlation |"
        ),
        (
            f"| Bounded anti-correlated | {bounded['target_sigma8']:.6g} | "
            f"{bounded['best_capacity']['max_sigma8']:.6g} | True | -1 | "
            "exact anti-correlation but cannot reach target |"
        ),
        "",
    ]
    if lensing is not None:
        lines.extend(
            [
                "## Lensing-Source Sigma8 Diagnostic",
                "",
                "| family | lensing sigma8 plus | density safe | sector correlation | reading |",
                "|---|---:|---|---:|---|",
            ]
        )
        for row in lensing["rows"]:
            lines.append(
                f"| {row['family']} | {row['lensing_sigma8_plus']:.6g} | "
                f"{row['positive_density_safe'] and row['negative_density_safe']} | "
                f"{row['sector_correlation']:.6g} | weak-field source diagnostic only |"
            )
        lines.extend(["", lensing["boundary"], ""])
    if projection is not None:
        lines.extend(
            [
                "## Weak-Lensing Projection Proxy",
                "",
                "| family | kappa proxy RMS | first k [1/Mpc] | first projected power | reading |",
                "|---|---:|---:|---:|---|",
            ]
        )
        for row in projection["rows"]:
            lines.append(
                f"| {row['family']} | {row['kappa_proxy_rms']:.6g} | "
                f"{row['first_k_center_inv_mpc']:.6g} | "
                f"{row['first_projected_power']:.6g} | uniform projection proxy only |"
            )
        lines.extend(["", projection["boundary"], ""])
    if janus_kernel is not None:
        lines.extend(
            [
                "## Janus Open-Distance Lensing Kernel",
                "",
                f"Source redshift: `{janus_kernel['source_redshift']:.6g}`, "
                f"peak weight redshift: `{janus_kernel['weight_argmax_redshift']:.6g}`.",
                "",
                "| family | kappa kernel RMS | first k [1/Mpc] | first projected power | reading |",
                "|---|---:|---:|---:|---|",
            ]
        )
        for row in janus_kernel["rows"]:
            lines.append(
                f"| {row['family']} | {row['kappa_janus_kernel_rms']:.6g} | "
                f"{row['first_k_center_inv_mpc']:.6g} | "
                f"{row['first_projected_power']:.6g} | Janus open-distance kernel only |"
            )
        lines.extend(["", janus_kernel["boundary"], ""])
    if shear is not None:
        lines.extend(
            [
                "## Janus Shear Proxy",
                "",
                "| family | kappa RMS | shear RMS | gamma1 RMS | gamma2 RMS | reading |",
                "|---|---:|---:|---:|---:|---|",
            ]
        )
        for row in shear["rows"]:
            lines.append(
                f"| {row['family']} | {row['kappa_kernel_rms']:.6g} | "
                f"{row['shear_proxy_rms']:.6g} | {row['gamma1_rms']:.6g} | "
                f"{row['gamma2_rms']:.6g} | E-mode proxy only |"
            )
        lines.extend(["", shear["boundary"], ""])
    if source_distribution is not None:
        lines.extend(
            [
                "## Janus Source-Distribution Lensing",
                "",
                f"Peak lens weight redshift: `{source_distribution['weight_argmax_redshift']:.6g}`.",
                "",
                "| family | kappa RMS | shear RMS | first shear power | reading |",
                "|---|---:|---:|---:|---|",
            ]
        )
        for row in source_distribution["rows"]:
            lines.append(
                f"| {row['family']} | {row['kappa_distribution_rms']:.6g} | "
                f"{row['shear_distribution_rms']:.6g} | "
                f"{row['first_shear_power']:.6g} | explicit source distribution only |"
            )
        lines.extend(["", source_distribution["boundary"], ""])
    if absolute_convergence is not None:
        lines.extend(
            [
                "## Janus Absolute Convergence",
                "",
                f"Peak coefficient redshift: `{absolute_convergence['coefficient_argmax_redshift']:.6g}`.",
                "",
                "| family | kappa abs RMS | shear abs RMS | first shear power | reading |",
                "|---|---:|---:|---:|---|",
            ]
        )
        for row in absolute_convergence["rows"]:
            lines.append(
                f"| {row['family']} | {row['kappa_abs_rms']:.6g} | "
                f"{row['shear_abs_rms']:.6g} | {row['first_shear_power']:.6g} | "
                "standard-prefactor scaffold |"
            )
        lines.extend(["", absolute_convergence["boundary"], ""])
    if lensing_audit is not None:
        lines.extend(
            [
                "## Lensing Normalization Audit",
                "",
                "| item | current status | next required |",
                "|---|---|---|",
            ]
        )
        for row in lensing_audit["rows"]:
            lines.append(
                f"| {row['item']} | {row['current_status']} | {row['next_required']} |"
            )
        lines.extend(["", lensing_audit["verdict"], ""])
        if "prefactor_decomposition" in lensing_audit:
            lines.extend(
                [
                    "### Prefactor Decomposition",
                    "",
                    "`C_J(a,z) = C_std * Q_source * Q_det * Q_cross * Q_proj * Q_dist`.",
                    "",
                    "| factor | status | rule |",
                    "|---|---|---|",
                ]
            )
            for row in lensing_audit["prefactor_decomposition"]:
                lines.append(f"| `{row['factor']}` | {row['status']} | {row['rule']} |")
            lines.append("")
    lines.extend(
        [
            "## Decision",
            "",
            "Do not select an IC transform as evidence. The admissible next step is to replace the standard-prefactor scaffold with a tensor-level Janus normalization and then use a stated survey `n(z_s)` before defining `S8_eff`.",
            "",
            "## Source Map",
            "",
            map_text,
            "",
        ]
    )
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")


if __name__ == "__main__":
    main()
