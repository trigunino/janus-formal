from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_explicit_action_test.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_explicit_action_test.json")


def build_payload() -> dict:
    action_terms = [
        {
            "term": "S_plus[g_plus,psi_plus]+S_minus[g_minus,psi_minus]",
            "role": "sector dynamics",
            "result": "keeps two geodesic families",
        },
        {
            "term": "int sqrt(-g_plus) Phi(g_plus, phi^*g_minus, L, T_plus, phi^*T_minus)",
            "role": "plus-covariant pulled-back coupling",
            "result": "defines K_plus and plus map equation",
        },
        {
            "term": "int sqrt(-g_minus) Phi_bar(g_minus, phi_*g_plus, L^{-1}, T_minus, phi_*T_plus)",
            "role": "minus-covariant mirror coupling",
            "result": "defines K_minus and minus map equation",
        },
        {
            "term": "lambda(L^T eta L-eta)+mu(phi_plus_to_minus o phi_minus_to_plus-id)",
            "role": "Lorentz and inverse-map constraints",
            "result": "keeps maps admissible but does not source-derive them",
        },
    ]
    variation_results = [
        {
            "variation": "delta g_plus",
            "gives": "K_plus",
            "passes": True,
        },
        {
            "variation": "delta g_minus",
            "gives": "K_minus",
            "passes": True,
        },
        {
            "variation": "delta phi",
            "gives": "E_phi map equation plus differential constraints",
            "passes": "formal",
        },
        {
            "variation": "delta L",
            "gives": "E_L algebraic/transport constraint",
            "passes": "formal",
        },
        {
            "variation": "plus and minus diffeomorphisms",
            "gives": "split Noether identities if both sector symmetries are independent",
            "passes": "conditional",
        },
    ]
    blockers = [
        "Phi/Phi_bar are arbitrary functions unless fixed by a principle",
        "two independent sector diffeomorphisms require nontrivial Stueckelberg restoration",
        "E_phi and E_L may overconstrain phi/L unless compatibility conditions hold",
        "boundary and gauge choices must be specified before observations",
    ]
    return {
        "description": "Explicit minimal Stueckelberg action test for Janus interaction closure.",
        "status": "explicit-action-conditional-pass-open",
        "new_axiom": True,
        "source_derived": False,
        "action_written": True,
        "defines_k_plus_k_minus": True,
        "defines_map_equations_formally": True,
        "split_noether_conditional": True,
        "unconditional_closure_proved": False,
        "physics_closed": False,
        "prediction_ready": False,
        "action_terms": action_terms,
        "variation_results": variation_results,
        "blockers": blockers,
        "acceptance_next": [
            "derive or choose Phi/Phi_bar from a no-fit principle",
            "prove compatibility of E_phi and E_L",
            "prove independent restored sector symmetries",
            "compute K_plus/K_minus for a tractable dust branch",
            "substitute and verify R_plus=R_minus=0",
        ],
        "verdict": (
            "The explicit Stueckelberg action passes the structural test: it can define "
            "K_plus, K_minus, map equations, and conditional split Noether identities. "
            "It is still a new axiom until Phi/Phi_bar and compatibility are fixed."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Stueckelberg Explicit Action Test",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"New axiom: {payload['new_axiom']}",
        f"Source derived: {payload['source_derived']}",
        f"Action written: {payload['action_written']}",
        f"Defines K_plus/K_minus: {payload['defines_k_plus_k_minus']}",
        f"Defines map equations formally: {payload['defines_map_equations_formally']}",
        f"Split Noether conditional: {payload['split_noether_conditional']}",
        f"Unconditional closure proved: {payload['unconditional_closure_proved']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Action Terms",
        "",
    ]
    for row in payload["action_terms"]:
        lines.append(f"- `{row['term']}`: {row['role']} -> {row['result']}")
    lines.extend(["", "## Variation Results", ""])
    for row in payload["variation_results"]:
        lines.append(f"- `{row['variation']}` gives {row['gives']}; passes={row['passes']}")
    lines.extend(["", "## Blockers", ""])
    lines.extend(f"- {item}" for item in payload["blockers"])
    lines.extend(["", "## Acceptance Next", ""])
    lines.extend(f"- {item}" for item in payload["acceptance_next"])
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
