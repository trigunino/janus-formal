from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/bianchi_mixed_transport_map_target.md")
JSON_PATH = Path("outputs/reports/bianchi_mixed_transport_map_target.json")


def build_payload() -> dict:
    definitions = [
        "K_plus^{mu nu} = Transport_{- to +}[T_minus, g_minus, g_plus, M_minus_to_plus]",
        "K_minus^{mu nu} = Transport_{+ to -}[T_plus, g_plus, g_minus, M_plus_to_minus]",
        "S_plus^{mu nu}=T_plus^{mu nu}+B_plus K_plus^{mu nu}",
        "S_minus^{mu nu}=B_minus K_minus^{mu nu}+T_minus^{mu nu}",
    ]
    residual_hooks = [
        "R_plus^mu = D_plus_nu S_plus^{mu nu}",
        "R_minus^mu = D_minus_nu S_minus^{mu nu}",
        "do not set R_plus/R_minus to zero until transport maps are derived",
    ]
    required_inputs = [
        "B_plus/B_minus determinant-volume branch",
        "M_minus_to_plus and M_plus_to_minus cross-sector frame/covector maps",
        "M_minus_to_plus induced by the same admissible L_minus_to_plus used by Q_cross",
        "dust/perfect-fluid/anisotropic stress case declaration",
        "connection difference C^a_bc=Gamma_plus^a_bc-Gamma_minus^a_bc",
        "Q_det density measure and Q_cross optical projection kept as separate factors",
    ]
    compatibility_requirements = [
        "Q_cross may use L_minus_to_plus only if the induced M_minus_to_plus also defines K_plus",
        "the mirror M_plus_to_minus must define K_minus",
        "both R_plus^mu=0 and R_minus^mu=0 are required before tensor lensing claims",
        "Q_cross is an optical contraction factor, not a divergence-transport factor",
    ]
    forbidden_shortcuts = [
        "K_plus=T_minus and K_minus=T_plus as generic closure",
        "absorbing Q_cross into Q_det",
        "using raw a_minus/a_plus scale ratio as transport amplitude",
        "claiming tensor lensing before both residuals are cancelled",
    ]
    return {
        "description": "Non-closure target for Bianchi-compatible mixed transport maps.",
        "source_anchors": [
            "Bianchi ansatz audit",
            "Bianchi mixed-stress residual target",
            "Q_det density-measure target",
            "Q_cross covariant projection target",
        ],
        "physics_closed": False,
        "definitions": definitions,
        "residual_hooks": residual_hooks,
        "required_inputs": required_inputs,
        "compatibility_requirements": compatibility_requirements,
        "forbidden_shortcuts": forbidden_shortcuts,
        "verdict": (
            "This names the mixed transport maps needed before Bianchi closure. "
            "It is not a solution and does not assert R_plus=R_minus=0."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Bianchi Mixed Transport Map Target",
        "",
        payload["description"],
        "",
        f"Physics closed: {payload['physics_closed']}",
        "",
        "## Definitions",
        "",
    ]
    lines.extend(f"- `{item}`" for item in payload["definitions"])
    lines.extend(["", "## Residual Hooks", ""])
    lines.extend(f"- `{item}`" for item in payload["residual_hooks"])
    lines.extend(["", "## Required Inputs", ""])
    lines.extend(f"- {item}" for item in payload["required_inputs"])
    lines.extend(["", "## Compatibility Requirements", ""])
    lines.extend(f"- {item}" for item in payload["compatibility_requirements"])
    lines.extend(["", "## Forbidden Shortcuts", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_shortcuts"])
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    return "\n".join(lines)


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(render_markdown(payload), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
