from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/qdet_density_measure_target.md")
JSON_PATH = Path("outputs/reports/qdet_density_measure_target.json")


def build_payload() -> dict:
    identities = {
        "determinant_bridge": "B_plus = sqrt(-g_minus / -g_plus)",
        "proper_to_effective_density": "rho_minus_eff = B_plus rho_minus_proper",
        "proper_source": (
            "R_plus_kk = chi A_plus [rho_plus - B_plus Q_cross |rho_minus_proper|]"
        ),
        "effective_source": (
            "R_plus_kk = chi A_plus [rho_plus - Q_cross rho_minus_eff]"
        ),
        "perfect_fluid_source": (
            "rho_s A_s -> (rho_s + p_s) A_s when pressure is not negligible"
        ),
        "anisotropic_stress_source": (
            "use full T_s^{mu nu} k_plus_mu k_plus_nu when stress is anisotropic"
        ),
    }
    branches = [
        {
            "name": "positive_effective",
            "input_density": "rho_minus_eff",
            "q_det": "1",
            "status": "current diagnostic convention",
            "rule": "Do not multiply by B_plus again.",
        },
        {
            "name": "negative_proper",
            "input_density": "rho_minus_proper",
            "q_det": "B_plus",
            "status": "derivation target",
            "rule": "Requires a derived positive optical volume map before numerical use.",
        },
        {
            "name": "raw_flrw_scale_ratio",
            "input_density": "unspecified",
            "q_det": "(a_minus/a_plus)^4",
            "status": "forbidden shortcut",
            "rule": "Not admissible until metric-volume and gauge conventions are derived.",
        },
    ]
    anti_double_counting_rules = [
        "Q_det acts on density measure/volume only.",
        "Q_cross acts on optical four-velocity/stress projection only.",
        "Use W_minus = Q_cross for positive_effective density.",
        "Use W_minus = B_plus Q_cross for negative_proper density.",
        "Never infer B_plus from survey data or from M20 a_minus/a_plus without the volume map.",
    ]
    missing = [
        "derive whether source inputs are positive-effective or negative-proper densities",
        "derive B_plus along the positive optical path, not as a raw global scale ratio",
        "state pressure/stress assumptions for T_minus before contracting with k_plus",
        "keep anisotropic stress as the full tensor contraction, not as a scalar density factor",
        "merge with the Q_cross L_minus_to_plus cross-map target without absorbing one factor into the other",
        "verify compatibility with Bianchi mixed-stress residuals",
    ]
    return {
        "description": "Density-measure target for the Janus Q_det determinant factor.",
        "source_anchors": [
            "M15 Eqs. 4a-4b determinant-coupled field equations.",
            "M30 Newtonian effective-density limit and determinant-ratio caveats.",
        ],
        "identities": identities,
        "branches": branches,
        "anti_double_counting_rules": anti_double_counting_rules,
        "missing_for_closure": missing,
        "physics_closed": False,
        "verdict": (
            "Q_det is reduced to a density-measure choice. The positive_effective "
            "branch is usable for diagnostics; negative_proper remains a derivation target."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Q_det Density-Measure Target",
        "",
        payload["description"],
        "",
        f"Physics closed: {payload['physics_closed']}",
        "",
        "## Identities",
        "",
    ]
    for key, value in payload["identities"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(
        [
            "",
            "## Branches",
            "",
            "| branch | input density | Q_det | status | rule |",
            "|---|---|---|---|---|",
        ]
    )
    for row in payload["branches"]:
        lines.append(
            f"| {row['name']} | `{row['input_density']}` | `{row['q_det']}` | "
            f"{row['status']} | {row['rule']} |"
        )
    lines.extend(["", "## Anti Double-Counting Rules", ""])
    lines.extend(f"- {item}" for item in payload["anti_double_counting_rules"])
    lines.extend(["", "## Missing For Closure", ""])
    lines.extend(f"- {item}" for item in payload["missing_for_closure"])
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
