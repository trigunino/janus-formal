from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_external_janus_omega_source_search_results import (
    build_payload as build_external_omega_search,
)
from scripts.build_p0_source_gap_scan_results import build_payload as build_gap_scan


REPORT_PATH = Path("outputs/reports/p0_sigma_source_traceability_gap_gate.md")
JSON_PATH = Path("outputs/reports/p0_sigma_source_traceability_gap_gate.json")


def build_payload() -> dict:
    external = build_external_omega_search()
    gap = build_gap_scan()
    sources = [
        {
            "source": "Janus official map/site",
            "url": "https://januscosmologicalmodel.com/map",
            "useful_for": "corpus and recent paper index",
            "sigma_dh_source_found": False,
        },
        {
            "source": "Petit, Margnat & Zejli 2024 EPJC / HAL bimetric model",
            "url": "https://hal.science/hal-04583560v1/document",
            "useful_for": "coupled field equations, determinant factors, Bianchi constraints",
            "sigma_dh_source_found": False,
        },
        {
            "source": "Petit & D'Agostini 2026 expansion exact solution note",
            "url": "https://www.jp-petit.org/papers/cosmo/2026-Expansion-exact-solution-2014-.pdf",
            "useful_for": "background expansion and Bianchi-condition context",
            "sigma_dh_source_found": False,
        },
        {
            "source": "Petit & D'Agostini 2026 questionable black holes",
            "url": "https://www.jp-petit.org/papers/cosmo/2026-01-12-Journal-of-Modern-Physics-QUESTIONABLE-BLACK-HOLES.pdf",
            "useful_for": "restates two coupled field equations and K/Kbar interaction tensors",
            "sigma_dh_source_found": False,
        },
    ]
    return {
        "description": "Traceability gap gate for a published Janus source of Sigma_alpha/D_alpha H or Phi_Sigma.",
        "status": "sigma-source-traceability-gap-open",
        "depends_on": [
            "p0_external_janus_omega_source_search_results",
            "p0_source_gap_scan_results",
        ],
        "latest_web_search_performed": True,
        "search_scope": [
            "Janus 2026 nonmetricity Sigma D_alpha H",
            "Janus bimetric action Lagrangian 2026",
            "Janus coupled field equations action nonmetricity",
        ],
        "sources_checked": sources,
        "external_omega_source_found": external["source_law_found"],
        "local_f_alpha_source_found": gap["f_alpha_source_found"],
        "published_sigma_dh_source_found": False,
        "published_phi_sigma_source_found": False,
        "published_nonmetricity_source_found": False,
        "closure_allowed_from_source": False,
        "prediction_ready": False,
        "allowed_next": [
            "derive Sigma/DH as original work from accepted Janus equations",
            "or add a clearly labeled new no-fit axiom and keep prediction blocked",
            "or prove no local low-derivative Janus source can select Sigma/DH",
        ],
        "guardrails": [
            "absence in this gate is not a proof of nonexistence; it is a traceability status",
            "do not cite Bianchi/K tensors as a Sigma/DH source unless they contain N_alpha or Phi_Sigma",
            "do not promote web-search snippets without PDF equation verification",
        ],
        "verdict": (
            "Current local and targeted external traceability does not find a published "
            "Janus equation selecting Sigma_alpha, D_alpha H, N_alpha or Phi_Sigma."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Sigma Source Traceability Gap Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Latest web search performed: {payload['latest_web_search_performed']}",
        f"Published Sigma/DH source found: {payload['published_sigma_dh_source_found']}",
        f"Published Phi_Sigma source found: {payload['published_phi_sigma_source_found']}",
        f"Published nonmetricity source found: {payload['published_nonmetricity_source_found']}",
        f"Closure allowed from source: {payload['closure_allowed_from_source']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Sources Checked",
        "",
        "| source | url | useful for | Sigma/DH source found |",
        "|---|---|---|---|",
    ]
    for row in payload["sources_checked"]:
        lines.append(
            f"| {row['source']} | {row['url']} | {row['useful_for']} | {row['sigma_dh_source_found']} |"
        )
    lines.extend(["", "## Allowed Next", ""])
    lines.extend(f"- {item}" for item in payload["allowed_next"])
    lines.extend(["", "## Guardrails", ""])
    lines.extend(f"- {item}" for item in payload["guardrails"])
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
