from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_f_decomposition_and_gauge.md")
JSON_PATH = Path("outputs/reports/p0_f_decomposition_and_gauge.json")


def build_payload() -> dict:
    decomposition = {
        "object": "Omega_alpha=(D_alpha L)L^{-1}",
        "lorentz_constraint": "Omega_{alpha AB}=-Omega_{alpha BA}",
        "components_per_alpha": 6,
        "split": [
            "3 boost components relative to transported u",
            "3 spatial rotation components in the rest-space of transported u",
        ],
    }
    dust_fixed_parts = [
        {
            "constraint": "receiver_force",
            "fixes": "boost/acceleration projection Omega_u acting on u",
            "does_not_fix": "spatial rotations about/inside the rest-space not seen by u u dust stress",
        },
        {
            "constraint": "transported_continuity",
            "fixes": "trace/divergence contraction F^A_{B A}u^B plus density-measure terms",
            "does_not_fix": "trace-free transverse Lorentz rotations",
        },
        {
            "constraint": "Q_cross along one ray",
            "fixes": "projection of transported u on that photon direction",
            "does_not_fix": "screen-plane rotations or directions not sampled by the ray",
        },
    ]
    gauge_candidates = [
        {
            "name": "fermi_walker_minimal_rotation",
            "condition": "set rest-space rotation of transported frame to zero along u",
            "status": "candidate gauge, not source-derived",
            "risk": "may be coordinate/frame choice rather than Janus physics",
        },
        {
            "name": "polar_lorentz_minimal_strain",
            "condition": "choose Lorentz projection closest to L_geom at each event",
            "status": "candidate gauge, not source-derived",
            "risk": "requires differentiable polar branch and may hide source dynamics",
        },
        {
            "name": "bianchi_solved_minimal_norm",
            "condition": "choose transverse Omega minimizing norm subject to R_plus=R_minus=0",
            "status": "diagnostic gauge",
            "risk": "variational criterion would be an added principle unless derived",
        },
    ]
    closure_implications = [
        "dust can constrain only the contractions of F seen by rho u u",
        "perfect-fluid pressure constrains additional isotropic rest-space pieces",
        "anisotropic stress Pi is needed to constrain full screen/rest-space tensor transport",
        "therefore dust closure alone cannot uniquely determine the full L transport",
    ]
    next_derivation_steps = [
        "derive Fermi-Walker/minimal-rotation branch residuals explicitly",
        "test whether perfect-fluid pressure removes part of the transverse freedom",
        "test whether anisotropic Pi transport fixes remaining screen rotations",
        "reject any gauge branch that changes Q_cross/K consistency or violates source traceability",
    ]
    return {
        "description": "Decomposition of F=D L into constrained Lorentz components and residual gauge freedom.",
        "status": "decomposition-open",
        "omega_decomposition_written": True,
        "dust_constraints_identified": True,
        "gauge_freedom_remaining": True,
        "unique_f_from_dust": False,
        "prediction_ready": False,
        "decomposition": decomposition,
        "dust_fixed_parts": dust_fixed_parts,
        "gauge_candidates": gauge_candidates,
        "closure_implications": closure_implications,
        "next_derivation_steps": next_derivation_steps,
        "verdict": (
            "Dust can close residual contractions conditionally but cannot determine "
            "all Lorentz transport components. A gauge or higher-matter tensor branch "
            "is required, and it must be source-derived before predictions."
        ),
    }


def render_markdown(payload: dict) -> str:
    d = payload["decomposition"]
    lines = [
        "# P0 F Decomposition And Gauge",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Omega decomposition written: {payload['omega_decomposition_written']}",
        f"Dust constraints identified: {payload['dust_constraints_identified']}",
        f"Gauge freedom remaining: {payload['gauge_freedom_remaining']}",
        f"Unique F from dust: {payload['unique_f_from_dust']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Decomposition",
        "",
        f"- object: `{d['object']}`",
        f"- Lorentz constraint: `{d['lorentz_constraint']}`",
        f"- components per alpha: {d['components_per_alpha']}",
    ]
    lines.extend(f"- split: {item}" for item in d["split"])
    lines.extend(["", "## Dust-Fixed Parts", ""])
    for row in payload["dust_fixed_parts"]:
        lines.append(f"- {row['constraint']}: fixes {row['fixes']}; does not fix {row['does_not_fix']}")
    lines.extend(["", "## Gauge Candidates", ""])
    for row in payload["gauge_candidates"]:
        lines.append(f"- {row['name']}: `{row['condition']}`; status={row['status']}; risk={row['risk']}")
    lines.extend(["", "## Closure Implications", ""])
    lines.extend(f"- {item}" for item in payload["closure_implications"])
    lines.extend(["", "## Next Derivation Steps", ""])
    lines.extend(f"- {item}" for item in payload["next_derivation_steps"])
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
