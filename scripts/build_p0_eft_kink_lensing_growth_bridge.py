from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_kink_lensing_growth_bridge.md")
JSON_PATH = Path("outputs/reports/p0_eft_kink_lensing_growth_bridge.json")


def build_payload() -> dict:
    lensing = {
        "kink_condition": "Delta(partial_n(Psi-Phi)) = Source_bnd(kappa,beta,lambda)",
        "value_slip": "not used; avoids coincident Green renormalization",
        "photon_effect": "refraction/kink in null geodesic extrinsic curvature",
        "status": "lensing_kink_ready_conditionally",
    }
    growth = {
        "density_contrast": "delta_m evolves under modified junction source",
        "growth_equation_target": "delta_m'' + 2H delta_m' - 4pi G_eff(k,z) rho delta_m = S_kink",
        "observable": "f_sigma8 from kink-modified growth equation",
        "status": "growth_solver_open",
    }
    theorem_status = {
        "ds_stability_ready_conditionally": True,
        "lensing_kink_ready_conditionally": True,
        "lensing_value_ready": False,
        "growth_equation_target_encoded": True,
        "growth_solver_implemented": False,
        "full_cosmology_prediction_ready": False,
    }
    obligations = [
        "derive S_kink contribution to the linear growth equation",
        "define G_eff(k,z) from transported active stress source",
        "implement a no-fit growth integrator for f_sigma8 under fixed Janus parameters",
    ]
    return {
        "description": "Kink-only lensing branch and growth-rate bridge after dS/Boundary closure.",
        "status": "kink-lensing-ready-growth-open",
        "lensing": lensing,
        "growth": growth,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "The safe observable branch is kink-only lensing. The next calculational step is "
            "the linear growth equation with S_kink and transported active stress."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Kink Lensing Growth Bridge",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## Lensing",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["lensing"].items())
    lines.extend(["", "## Growth"])
    lines.extend(f"- {key}: {value}" for key, value in payload["growth"].items())
    lines.extend(["", "## Status"])
    lines.extend(f"- {key}: {value}" for key, value in payload["theorem_status"].items())
    lines.extend(["", "## Obligations"])
    lines.extend(f"- {item}" for item in payload["obligations"])
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
