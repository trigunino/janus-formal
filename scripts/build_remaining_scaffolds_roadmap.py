from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/remaining_scaffolds_roadmap.md")
JSON_PATH = Path("outputs/reports/remaining_scaffolds_roadmap.json")


def build_payload() -> dict:
    tracks = [
        {
            "track": "Bianchi closure",
            "owner": "math-source",
            "current": "weak-field branches only",
            "replacement": "mixed stress tensors satisfying both coupled divergences",
            "blocks": ["tensor lensing", "S8_eff", "exact coupled solver"],
            "parallelizable": True,
        },
        {
            "track": "Q_det",
            "owner": "metric-volume",
            "current": "positive_effective density convention",
            "replacement": "source-derived metric-volume map between proper and positive-effective densities",
            "blocks": ["absolute lensing", "negative-sector weight"],
            "parallelizable": True,
        },
        {
            "track": "Q_cross",
            "owner": "tetrad-map",
            "current": "equal projection plus local velocity bridge",
            "replacement": "global L_minus_to_plus tetrad-map projection along positive null rays",
            "blocks": ["PM lensing source", "absolute lensing"],
            "parallelizable": True,
        },
        {
            "track": "IC and velocity field",
            "owner": "simulation",
            "current": "bounded/analytic diagnostic IC",
            "replacement": "Janus-derived transfer function, amplitude and initial velocity field",
            "blocks": ["production PM", "sigma8/S8 interpretation"],
            "parallelizable": True,
        },
        {
            "track": "Survey layer",
            "owner": "observational",
            "current": "interface only",
            "replacement": "declared n(z), tomographic bins, observed vector, covariance, mask/window",
            "blocks": ["survey comparison", "S8_eff"],
            "parallelizable": True,
        },
        {
            "track": "Shear screen",
            "owner": "optics",
            "current": "standard E-mode Fourier relation",
            "replacement": "proof Janus optical screen reduces to standard weak-shear operator or explicit replacement",
            "blocks": ["shear likelihood"],
            "parallelizable": True,
        },
        {
            "track": "Metric potential / Weyl",
            "owner": "metric-perturbation",
            "current": "weak-field Poisson/Weyl diagnostic chain",
            "replacement": "source-derived h_plus, gauge/slip and source identity before promoting Phi_lens_plus",
            "blocks": ["tensor lensing", "shear likelihood", "S8_eff"],
            "parallelizable": True,
        },
    ]
    keepers = [
        "H0^-1 PM time calibration unless full Janus PM equations replace it",
        "factorized C_J map; fill factors, do not fit a scalar patch",
        "dipole-repeller annular shape diagnostic as shape-only observable target",
    ]
    return {
        "description": "Coordination roadmap for remaining Janus scaffolds.",
        "tracks": tracks,
        "keepers": keepers,
        "verdict": (
            "Work can proceed in parallel, but final claims require merging the "
            "Bianchi, Q_det, Q_cross, IC, metric-potential, shear-screen and survey tracks."
        ),
    }


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")

    lines = [
        "# Remaining Scaffolds Roadmap",
        "",
        payload["description"],
        "",
        "| track | owner | current | replacement | blocks | parallelizable |",
        "|---|---|---|---|---|---|",
    ]
    for row in payload["tracks"]:
        lines.append(
            f"| {row['track']} | {row['owner']} | {row['current']} | "
            f"{row['replacement']} | {', '.join(row['blocks'])} | {row['parallelizable']} |"
        )
    lines.extend(["", "## Keepers", ""])
    lines.extend(f"- {item}" for item in payload["keepers"])
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
