from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/bianchi_mixed_stress_residual_target.md")
JSON_PATH = Path("outputs/reports/bianchi_mixed_stress_residual_target.json")


def build_payload() -> dict:
    identities = [
        "B_plus = sqrt(-g_minus / -g_plus)",
        "B_minus = sqrt(-g_plus / -g_minus)",
        "B_plus * B_minus = 1",
        "C^a_bc = Gamma_plus^a_bc - Gamma_minus^a_bc",
        "partial_nu ln(B_plus) = -C^a_{a nu}",
        "partial_nu ln(B_minus) = C^a_{a nu}",
    ]
    sources = [
        "S_plus^{mu nu} = T_plus^{mu nu} + B_plus K_plus^{mu nu}",
        "S_minus^{mu nu} = B_minus K_minus^{mu nu} + T_minus^{mu nu}",
    ]
    residuals = [
        {
            "sector": "positive",
            "residual": (
                "R_plus^mu = D_plus_nu T_plus^{mu nu} "
                "+ B_plus (D_minus_nu K_plus^{mu nu} "
                "+ C^mu_{nu a} K_plus^{a nu})"
            ),
            "closure": "R_plus^mu = 0",
        },
        {
            "sector": "negative",
            "residual": (
                "R_minus^mu = D_minus_nu T_minus^{mu nu} "
                "+ B_minus (D_plus_nu K_minus^{mu nu} "
                "- C^mu_{nu a} K_minus^{a nu})"
            ),
            "closure": "R_minus^mu = 0",
        },
    ]
    optical_slot = [
        "R_plus_kk = chi A_plus [rho_plus - B_plus Q_cross |rho_minus|]",
        "Q_det = B_plus",
        "Q_cross = A_minus / A_plus",
        "Q_cross is readable from R_plus_kk only after K_plus/K_minus satisfy both Bianchi residuals",
    ]
    forbidden_uses = [
        "do not insert an independently chosen Q_cross into tensor claims before R_plus^mu=0",
        "do not insert an independently chosen Q_cross into tensor claims before R_minus^mu=0",
        "do not absorb Q_cross into K_plus/K_minus divergence transport",
    ]
    return {
        "description": "Residual target for Bianchi-compatible Janus mixed stress tensors.",
        "source_anchors": [
            "M15 Eqs. 4a-4b",
            "M30 Sect. 12-14 and Eqs. 105a-105b",
        ],
        "status": "derivation-target",
        "physics_closed": False,
        "identities": identities,
        "mixed_sources": sources,
        "residuals": residuals,
        "optical_slot": optical_slot,
        "forbidden_uses": forbidden_uses,
        "hard_missing_term": "connection-difference force term C^mu_{nu a} K^{a nu}",
        "verdict": (
            "This reduces the Bianchi scaffold to explicit residuals. It does not "
            "supply K_plus/K_minus, so tensor lensing remains blocked."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Bianchi Mixed-Stress Residual Target",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Physics closed: {payload['physics_closed']}",
        "",
        "## Source Anchors",
        "",
    ]
    lines.extend(f"- {item}" for item in payload["source_anchors"])
    lines.extend(["", "## Identities", ""])
    lines.extend(f"- `{item}`" for item in payload["identities"])
    lines.extend(["", "## Mixed Sources", ""])
    lines.extend(f"- `{item}`" for item in payload["mixed_sources"])
    lines.extend(
        [
            "",
            "## Residuals",
            "",
            "| sector | residual | closure |",
            "|---|---|---|",
        ]
    )
    for row in payload["residuals"]:
        lines.append(f"| {row['sector']} | `{row['residual']}` | `{row['closure']}` |")
    lines.extend(["", "## Optical Slot", ""])
    lines.extend(f"- `{item}`" for item in payload["optical_slot"])
    lines.extend(["", "## Forbidden Uses", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_uses"])
    lines.extend(
        [
            "",
            f"Hard missing term: `{payload['hard_missing_term']}`.",
            "",
            f"Verdict: {payload['verdict']}",
            "",
        ]
    )
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
