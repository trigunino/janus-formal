from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_vlasov_torsion_coupling.md")
JSON_PATH = Path("outputs/reports/p0_eft_vlasov_torsion_coupling.json")


def build_payload() -> dict:
    sectors = {
        "spinless_matter": "minimal collisionless particles follow metric geodesic Vlasov; torsion couples only through effective metric/bridge",
        "spinning_matter": "Papapetrou/Einstein-Cartan force can add q_T/q_A spin-torsion terms",
        "fluid_closure": "rho, p, Pi require moments of f plus spin density if spinning sector is retained",
    }
    torsion_force = {
        "generic_form": "L f + F_torsion^i partial_{p_i} f = 0",
        "spinless_result": "F_torsion=0 for minimal spinless test particles",
        "spinning_open": "F_torsion depends on spin density S^{mu nu} and contorsion gradients",
        "slip_relevance": "anisotropic stress Pi can source Phi-Psi and lensing/growth",
    }
    theorem_status = {
        "spinless_vlasov_torsion_force_closed_zero": True,
        "spinning_vlasov_torsion_force_derived": False,
        "fluid_moments_closed_spinless": False,
        "anisotropic_stress_pi_closed": False,
        "lensing_growth_sources_closed": False,
        "prediction_ready_unconditional": False,
    }
    obligations = [
        "compute spinless stress-tensor moments with active B4vol measure",
        "decide whether spinning matter sector is retained or integrated out",
        "if retained, derive Papapetrou/contorsion force and spin moment hierarchy",
        "derive slip/lensing source from Pi",
    ]
    return {
        "description": "Torsion coupling audit for Vlasov/matter after dS boundary closure.",
        "status": "spinless-torsion-force-zero-spinning-open",
        "sectors": sectors,
        "torsion_force": torsion_force,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "For minimal spinless Vlasov matter, torsion does not add a direct force term. "
            "Torsion enters through metric/bridge/source measure. Spinning matter remains open."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Vlasov Torsion Coupling",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## Sectors",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["sectors"].items())
    lines.extend(["", "## Torsion Force"])
    lines.extend(f"- {key}: {value}" for key, value in payload["torsion_force"].items())
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
