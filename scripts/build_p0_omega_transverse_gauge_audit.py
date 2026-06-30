from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_omega_transverse_gauge_audit.md")
JSON_PATH = Path("outputs/reports/p0_omega_transverse_gauge_audit.json")


def build_payload() -> dict:
    decomposition = {
        "omega": "Omega_alpha=(D_alpha L)L^{-1}",
        "constraint": "Omega_{alpha AB}=-Omega_{alpha BA}",
        "per_alpha_components": 6,
        "dust_visible": [
            "one trace/divergence contraction from densitized continuity",
            "three boost/acceleration projections from receiver-force equation",
        ],
        "dust_invisible": [
            "rest-space rotations not acting on rho u u",
            "screen rotations not sampled by a single optical ray",
            "transverse derivatives not entering the dust divergence contraction",
        ],
    }
    gauge_lifting_options = [
        {
            "option": "minimal_rotation",
            "condition": "projected rest-space rotation is set to zero",
            "status": "gauge candidate",
            "source_derived": False,
        },
        {
            "option": "anisotropic_Pi_axes",
            "condition": "nondegenerate Pi eigenvectors define physical rest-space axes",
            "status": "matter constraint candidate",
            "source_derived": False,
        },
        {
            "option": "boundary_initial_L",
            "condition": "boundary/initial tetrad alignment plus PDE propagation fixes residual freedom",
            "status": "boundary-value candidate",
            "source_derived": False,
        },
        {
            "option": "action_principle_for_L",
            "condition": "additional variational principle selects Omega among PDE solutions",
            "status": "new axiom/source target",
            "source_derived": False,
        },
    ]
    implication_for_qcross = [
        "Q_cross using one photon direction constrains only the contraction sampled by that ray",
        "screen rotations may affect shear/polarization observables if Pi or multi-ray structure is present",
        "do not tune transverse gauge to fit lensing; it must be fixed before survey comparison",
    ]
    return {
        "description": "P0 audit of transverse gauge freedom remaining in Omega/F_alpha after dust PDE constraints.",
        "status": "transverse-gauge-open",
        "omega_decomposed": True,
        "dust_does_not_fix_unique_omega": True,
        "gauge_lifting_options_written": True,
        "unique_omega_found": False,
        "physics_closed": False,
        "prediction_ready": False,
        "decomposition": decomposition,
        "gauge_lifting_options": gauge_lifting_options,
        "implication_for_qcross": implication_for_qcross,
        "verdict": (
            "Dust PDE constraints are insufficient for a unique Lorentz transport. "
            "A physical orientation source, boundary condition, or new variational "
            "principle is required before Q_cross can be predictive."
        ),
    }


def render_markdown(payload: dict) -> str:
    d = payload["decomposition"]
    lines = [
        "# P0 Omega Transverse Gauge Audit",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Omega decomposed: {payload['omega_decomposed']}",
        f"Dust does not fix unique Omega: {payload['dust_does_not_fix_unique_omega']}",
        f"Unique Omega found: {payload['unique_omega_found']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Decomposition",
        "",
        f"- omega: `{d['omega']}`",
        f"- constraint: `{d['constraint']}`",
        f"- per-alpha components: {d['per_alpha_components']}",
        "",
        "Dust visible:",
    ]
    lines.extend(f"- {item}" for item in d["dust_visible"])
    lines.extend(["", "Dust invisible:"])
    lines.extend(f"- {item}" for item in d["dust_invisible"])
    lines.extend(["", "## Gauge Lifting Options", ""])
    for row in payload["gauge_lifting_options"]:
        lines.append(
            f"- {row['option']}: {row['condition']}; status={row['status']}; source_derived={row['source_derived']}"
        )
    lines.extend(["", "## Implication For Q_cross", ""])
    lines.extend(f"- {item}" for item in payload["implication_for_qcross"])
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.parent.mkdir(parents=True, exist_ok=True)
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
