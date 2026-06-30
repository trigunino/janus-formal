from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_b4vol_solder_derivation.md")
JSON_PATH = Path("outputs/reports/p0_eft_b4vol_solder_derivation.json")


def build_payload() -> dict:
    solder = {
        "tetrad_bridge": "E_other_to_self = L_solder * E_other pulled to the self frame",
        "determinant": "det(E_other_to_self) = det(L_solder) * det(E_other)",
        "b4vol": "B4vol = det(E_other_to_self)/det(E_self)",
        "log_link": "log B4vol = log det(E_other_to_self) - log det(E_self)",
        "lambda_link": "same determinant jump source used in volume/solder lambda closure",
    }
    mass_shell = {
        "receiver_measure": "dPi_self = sqrt(-g_self) d^3p_self / p_self^0",
        "transported_measure": "dPi_other_to_self = B4vol * J_shell/lapse * dPi_self",
        "liouville_jacobian": "canonical phase-space lift gives J_full=1",
        "remaining_factor": "mass-shell reduction leaves receiver energy/lapse normalization",
    }
    theorem_status = {
        "b4vol_derived_from_tetrad_soldering": True,
        "b4vol_linked_to_lambda_logdet": True,
        "liouville_jacobian_kept_separate": True,
        "mass_shell_lapse_factor_identified": True,
        "mass_shell_lapse_factor_closed": False,
        "active_source_measure_closed": False,
        "prediction_ready_unconditional": False,
    }
    obligations = [
        "derive det(L_solder) from the same-L/tetrad compatibility condition",
        "compute the receiver p^0/lapse factor on the selected dS branch",
        "then insert B4vol into T_other_to_self moments",
    ]
    return {
        "description": "B4vol derivation from tetrad soldering and link to volume/solder lambda.",
        "status": "b4vol-derived-lapse-factor-open",
        "solder": solder,
        "mass_shell": mass_shell,
        "theorem_status": theorem_status,
        "obligations": obligations,
        "verdict": (
            "B4vol is derived as the determinant ratio of the tetrad soldering and is linked "
            "to the same log-det source used for lambda. Active source measure still needs "
            "det(L_solder) and mass-shell lapse/energy normalization."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT B4vol Solder Derivation",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## Solder",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["solder"].items())
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
