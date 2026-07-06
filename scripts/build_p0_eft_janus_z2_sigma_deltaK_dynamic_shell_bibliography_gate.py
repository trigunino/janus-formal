from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_deltaK_dynamic_shell_bibliography_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_deltaK_dynamic_shell_bibliography_gate.json"
)


def build_payload() -> dict:
    sources = [
        {
            "id": "poisson-visser-1995",
            "url": "https://arxiv.org/abs/gr-qc/9506083",
            "supports": "thin-shell wormhole throat radius to extrinsic-curvature jump and stability logic",
        },
        {
            "id": "lobo-crawford-2005",
            "url": "https://arxiv.org/abs/gr-qc/0507063",
            "supports": "dynamic thin-shell conservation equation with momentum-flux term",
        },
        {
            "id": "ishak-lake-transparent-shells",
            "url": "https://arxiv.org/abs/gr-qc/0108058",
            "supports": "transparent spherical shell conditions",
        },
        {
            "id": "eiroa-2008",
            "url": "https://arxiv.org/abs/0805.1403",
            "supports": "general spherical thin-shell stability potential template",
        },
        {
            "id": "sahu-2024",
            "url": "https://arxiv.org/abs/2402.09539",
            "supports": "cosmological thin-shell hypersurface introduction and matching",
        },
        {
            "id": "mars-senovilla-2002",
            "url": "https://arxiv.org/abs/gr-qc/0201054",
            "supports": "general hypersurface junction/rigging/Bianchi distribution guard",
        },
    ]
    return {
        "status": "janus-z2-sigma-deltaK-dynamic-shell-bibliography-gate",
        "active_core": "Z2_tunnel_Sigma",
        "sources": sources,
        "deltaK_formula_supported": True,
        "momentum_flux_formula_supported": True,
        "transparent_shell_route_supported": True,
        "bulk_functions_f_pm_required": True,
        "Janus_specific_f_pm_derived": False,
        "gate_passed": True,
        "next_required": [
            "derive active f_plus(R), f_minus(R) from Z2/Sigma bulk metric branch",
            "derive Rdot and Rddot in shell proper-time gauge",
            "then instantiate RSigmaToDeltaKFormulaGate",
        ],
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Janus Z2/Sigma DeltaK Dynamic Shell Bibliography Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Janus-specific f_pm derived: `{payload['Janus_specific_f_pm_derived']}`",
        "",
        "## Sources",
    ]
    lines.extend(f"- `{row['id']}`: {row['url']} ({row['supports']})" for row in payload["sources"])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    return "\n".join(lines)


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(render_markdown(payload), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
