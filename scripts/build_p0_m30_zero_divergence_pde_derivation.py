from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_m30_zero_divergence_pde_derivation.md")
JSON_PATH = Path("outputs/reports/p0_m30_zero_divergence_pde_derivation.json")


def build_payload() -> dict:
    source_principles = [
        {
            "source": "M30 Sect. 14 / conclusion",
            "principle": "the exact interaction tensor is determined by the zero-divergence condition",
            "status": "source-principle",
        },
        {
            "source": "M15/M30 coupled field equations",
            "principle": "mixed source terms carry determinant ratios sqrt(-g_other/-g_self)",
            "status": "source-principle",
        },
    ]
    pde_system = [
        {
            "sector": "plus",
            "unknown": "K_plus^{mu nu}",
            "equation": "D_plus_nu(B_4vol_plus_from_minus K_plus^{mu nu}) = -D_plus_nu T_plus^{mu nu}",
            "conserved_reduction": "if D_plus_nu T_plus^{mu nu}=0 then D_plus_nu(B_4vol_plus_from_minus K_plus^{mu nu})=0",
            "status": "source-derived PDE target",
        },
        {
            "sector": "minus",
            "unknown": "K_minus^{mu nu}",
            "equation": "D_minus_nu(B_4vol_minus_from_plus K_minus^{mu nu}) = -D_minus_nu T_minus^{mu nu}",
            "conserved_reduction": "if D_minus_nu T_minus^{mu nu}=0 then D_minus_nu(B_4vol_minus_from_plus K_minus^{mu nu})=0",
            "status": "source-derived PDE target",
        },
    ]
    link_to_f_alpha = [
        "If K is parameterized by transported matter, K_plus=T_minus transported by L_minus_to_plus, the PDE becomes a constraint on F_alpha=(D_alpha L)L^{-1}",
        "The PDE fixes only the divergence-visible contractions of F_alpha, not all Lorentz gauge components",
        "F_alpha must still satisfy F_alpha^T eta + eta F_alpha=0 if L is used for K/Q_cross",
        "Additional gauge or matter tensor constraints are needed for uniqueness",
    ]
    solved_now = [
        "the minimal axiom D S=0 is no longer arbitrary: it is the M30 zero-divergence PDE target",
        "B_4vol product-rule terms remain inside the PDE",
        "R_plus/R_minus closure is reduced to solving this PDE plus same-sector conservation",
    ]
    still_open = [
        "closed-form K_plus/K_minus solution",
        "unique F_alpha for a transported-matter parameterization",
        "boundary/initial conditions for the divergence PDE",
        "pressure/projector/Pi extension",
        "proof that the same solution gives physical Q_cross normalization",
    ]
    return {
        "description": "P0 derivation of the M30 zero-divergence principle as a PDE for interaction tensors.",
        "status": "source-derived-pde-open",
        "zero_divergence_principle_source_anchored": True,
        "pde_system_written": True,
        "b4vol_inside_pde": True,
        "f_alpha_constrained_not_solved": True,
        "conditional_r_plus_closed": True,
        "conditional_r_minus_closed": True,
        "unique_solution_found": False,
        "physics_closed": False,
        "prediction_ready": False,
        "source_principles": source_principles,
        "pde_system": pde_system,
        "link_to_f_alpha": link_to_f_alpha,
        "solved_now": solved_now,
        "still_open": still_open,
        "verdict": (
            "A real source-derived route exists: solve the zero-divergence PDE for the "
            "mixed interaction tensors. This upgrades the minimal axiom branch into a "
            "source-anchored PDE target, but it does not yet provide a unique K or F_alpha."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 M30 Zero-Divergence PDE Derivation",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Zero-divergence principle source anchored: {payload['zero_divergence_principle_source_anchored']}",
        f"PDE system written: {payload['pde_system_written']}",
        f"B_4vol inside PDE: {payload['b4vol_inside_pde']}",
        f"F_alpha constrained not solved: {payload['f_alpha_constrained_not_solved']}",
        f"Unique solution found: {payload['unique_solution_found']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Source Principles",
        "",
    ]
    for row in payload["source_principles"]:
        lines.append(f"- {row['source']}: {row['principle']} ({row['status']})")
    lines.extend(["", "## PDE System", ""])
    for row in payload["pde_system"]:
        lines.append(f"- {row['sector']}: `{row['equation']}`")
        lines.append(f"  - unknown: `{row['unknown']}`")
        lines.append(f"  - conserved reduction: `{row['conserved_reduction']}`")
        lines.append(f"  - status: {row['status']}")
    lines.extend(["", "## Link To F_alpha", ""])
    lines.extend(f"- {item}" for item in payload["link_to_f_alpha"])
    lines.extend(["", "## Solved Now", ""])
    lines.extend(f"- {item}" for item in payload["solved_now"])
    lines.extend(["", "## Still Open", ""])
    lines.extend(f"- {item}" for item in payload["still_open"])
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
