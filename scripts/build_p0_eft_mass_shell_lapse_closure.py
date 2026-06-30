from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_mass_shell_lapse_closure.md")
JSON_PATH = Path("outputs/reports/p0_eft_mass_shell_lapse_closure.json")


def build_payload() -> dict:
    det_l = {
        "same_L_tetrad_compatibility": "L_solder is Lorentz/tetrad-compatible",
        "det_L_solder": "+/-1",
        "orientation_selected": "Pin-/PT branch fixes the sign; absolute volume uses |det L_solder|=1",
        "b4vol_reduced": "B4vol = det(E_other)/det(E_self) up to orientation sign",
    }
    mass_shell = {
        "receiver_energy": "p_self^0 = sqrt(m^2 + h_self^{ij} p_i p_j)/N_self",
        "measure_factor": "dPi_self = sqrt(h_self) d^3p / p_self^0",
        "transport_factor": "canonical Liouville Jacobian is 1; mass-shell factor is receiver p^0/lapse",
        "status": "closed on selected dS receiver lapse N_self",
    }
    theorem_status = {
        "det_L_solder_closed_abs": True,
        "b4vol_reduced_to_tetrad_det_ratio": True,
        "receiver_p0_lapse_factor_closed": True,
        "active_source_measure_closed_conditionally": True,
        "prediction_ready_unconditional": False,
    }
    obligations = [
        "insert active source measure into T_other_to_self moments",
        "separate spinless Vlasov from spin-torsion kinetic corrections",
    ]
    return {
        "description": "Mass-shell lapse and det(L_solder) closure for active source measure.",
        "status": "active-source-measure-conditionally-closed",
        "det_l": det_l,
        "mass_shell": mass_shell,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "det(L_solder) closes in absolute value by Lorentz/tetrad compatibility, and the "
            "mass-shell factor closes on the selected dS receiver lapse. Active source measure "
            "is conditionally ready for moment construction."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Mass-Shell Lapse Closure",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## det(L)",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["det_l"].items())
    lines.extend(["", "## Mass Shell"])
    lines.extend(f"- {key}: {value}" for key, value in payload["mass_shell"].items())
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
