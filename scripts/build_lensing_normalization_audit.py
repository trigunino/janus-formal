from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/lensing_normalization_audit.md")
JSON_PATH = Path("outputs/reports/lensing_normalization_audit.json")


ROWS = [
    {
        "item": "Positive-sector photon path",
        "basis": "M15/M30 two metric/geodesic families",
        "current_status": "accepted source-backed",
        "code_surface": "docs trace only",
        "next_required": "Geodesic ray-tracing equations for positive photons.",
    },
    {
        "item": "Weak-field lensing source",
        "basis": "M15/M30 Newtonian signs plus M07/M20 lensing anchors",
        "current_status": "implemented diagnostic",
        "code_surface": "positive_photon_lensing_contrast",
        "next_required": "Tensor-level derivation of the same source in the optical limit.",
    },
    {
        "item": "Negative hole gives positive lensing source",
        "basis": "M07 verified-concept anchor",
        "current_status": "implemented sign check",
        "code_surface": "tests/test_lensing.py",
        "next_required": "Quantitative lensing amplitude from Janus geodesics.",
    },
    {
        "item": "Open-distance geometry",
        "basis": "M18 r=sinh(2(u0-u))",
        "current_status": "accepted working geometry",
        "code_surface": "janus_open_lensing_geometry_kernel",
        "next_required": "Re-open only if a peer-reviewed Janus source changes the positive optical metric.",
    },
    {
        "item": "Determinant-ratio gauge",
        "basis": "M15 determinant roots; M20 scale-factor ratio; M30 Newtonian det-ratio ~= 1",
        "current_status": "open gauge/measure blocker",
        "code_surface": "positive_photon_lensing_source_grid_with_density_convention",
        "next_required": "Derive the compatible volume convention before using any a_-/a_+ value in lensing.",
    },
    {
        "item": "Source redshift distribution",
        "basis": "explicit input, not fitted",
        "current_status": "prototype",
        "code_surface": "janus_source_distribution_lensing_weights",
        "next_required": "Replace default diagnostic distribution by a cited survey n(z_s).",
    },
    {
        "item": "E-mode shear relation",
        "basis": "standard weak-lensing Fourier relation",
        "current_status": "standard proxy",
        "code_surface": "shear_from_convergence_proxy_2d",
        "next_required": "Replace only if Janus optical geodesics modify the relation.",
    },
    {
        "item": "Absolute convergence prefactor",
        "basis": "standard weak-lensing normalization",
        "current_status": "scaffold",
        "code_surface": "janus_absolute_lensing_coefficients",
        "next_required": "Derive Janus tensor normalization and the correct Omega_eff.",
    },
    {
        "item": "Growth and transfer function",
        "basis": "toy IC diagnostics only",
        "current_status": "missing",
        "code_surface": "IC scripts and PM prototypes",
        "next_required": "Derive a Janus positive-density two-sector transfer/growth model.",
    },
    {
        "item": "Survey likelihood",
        "basis": "none yet",
        "current_status": "missing",
        "code_surface": "none",
        "next_required": "Add covariance, masks, noise, redshift bins and systematics.",
    },
    {
        "item": "S8_eff compression",
        "basis": "blocked until above terms are fixed",
        "current_status": "not admissible yet",
        "code_surface": "formal/axioms/sigma8_observable_map.md",
        "next_required": "Define only after field, kernel, normalization and likelihood are fixed.",
    },
]


PREFACTOR_DECOMPOSITION = [
    {
        "factor": "C_std",
        "meaning": "(3/2) Omega_abs (H0/c)^2",
        "status": "implemented scaffold",
        "rule": "May be replaced only by tensor-derived C_J.",
    },
    {
        "factor": "Q_source",
        "meaning": "rho_+ - |rho_-| optical source reduction",
        "status": "checked under equal-projection and B=1 assumptions",
        "rule": "No free amplitude; derive from R(+)kk.",
    },
    {
        "factor": "Q_det",
        "meaning": "determinant-ratio correction from sqrt((-g_-)/(-g_+))",
        "status": "source becomes rho_+ - B|rho_-|; M20 gives a_-/a_+ ~= 1/100 but M30 uses det-ratio ~= 1 in Newtonian limit",
        "rule": "Use explicit density convention; do not plug in (a_-/a_+)^4 until metric-volume mapping is derived.",
    },
    {
        "factor": "Q_cross",
        "meaning": "negative-sector optical projection ratio via L_minus_to_plus tetrad/covector map",
        "status": "isolated symbolically; equal-projection limit gives current source",
        "rule": "Do not set non-unity values until L_minus_to_plus is derived; Q_cross=1 only under an explicit equal-projection assumption.",
    },
    {
        "factor": "Q_proj",
        "meaning": "optical projection A=(u.k)^2 and screen normalization",
        "status": "accepted working result: positive FLRW Jacobi reduction gives 1+z",
        "rule": "Do not fit; rederive only if peer-reviewed Janus optics changes affine-distance conversion.",
    },
    {
        "factor": "Q_dist",
        "meaning": "optical angular-diameter distance replacement",
        "status": "accepted working result: M18 open marker gives optical comoving/angular kernels",
        "rule": "Do not fit; rederive only if peer-reviewed Janus optics differs from M18 open geometry.",
    },
]


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "description": "Audit of Janus weak-lensing normalization dependencies.",
        "evidence_policy": (
            "Accepted derivation anchors are M15/M30 for positive geodesics and coupled "
            "field equations, M18 for the open-distance geometry, and M07 only as an "
            "accepted-publication concept anchor for negative lensing. Recent author "
            "documents remain roadmap material unless independently accepted or verified."
        ),
        "verdict": (
            "Current absolute convergence is a controlled diagnostic. It is not yet a "
            "survey-level Janus S8 prediction because the absolute prefactor, optical "
            "distance validation, growth model and survey likelihood remain open."
        ),
        "prefactor_decomposition": PREFACTOR_DECOMPOSITION,
        "rows": ROWS,
    }
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")

    lines = [
        "# Lensing Normalization Audit",
        "",
        payload["description"],
        "",
        f"Evidence policy: {payload['evidence_policy']}",
        "",
        "| item | basis | current status | code surface | next required |",
        "|---|---|---|---|---|",
    ]
    for row in ROWS:
        lines.append(
            f"| {row['item']} | {row['basis']} | {row['current_status']} | "
            f"`{row['code_surface']}` | {row['next_required']} |"
        )
    lines.extend(
        [
            "",
            "## Prefactor Decomposition",
            "",
            "No scalar correction may be fitted. A Janus coefficient must be derived as:",
            "",
            "```text",
            "C_J(a,z) = C_std * Q_source * Q_det * Q_cross * Q_proj * Q_dist",
            "```",
            "",
            "| factor | meaning | status | rule |",
            "|---|---|---|---|",
        ]
    )
    for row in PREFACTOR_DECOMPOSITION:
        lines.append(
            f"| `{row['factor']}` | {row['meaning']} | {row['status']} | {row['rule']} |"
        )
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
