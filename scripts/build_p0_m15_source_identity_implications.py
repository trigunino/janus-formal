from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_m15_source_identity_implications.md")
JSON_PATH = Path("outputs/reports/p0_m15_source_identity_implications.json")


def build_payload() -> dict:
    source_anchors = [
        {
            "anchor": "M15 Eq. 14 Janus variation link",
            "content": "delta g_plus^{mu nu} = - delta g_minus^{mu nu}",
            "implies": "coupled variations, not a cross-tetrad transport law",
            "closes": [],
        },
        {
            "anchor": "M15 Eqs. 23a-23b coupled field equations",
            "content": "G_plus = chi(T_plus + sqrt(-g_minus/-g_plus) T_minus); G_minus = -chi(sqrt(-g_plus/-g_minus) T_plus + T_minus)",
            "implies": "B_4vol determinant factors are source-level field-equation factors",
            "closes": ["B_4vol definition"],
        },
        {
            "anchor": "M15 Eq. 7 FLRW determinant specialization",
            "content": "g_plus=-(a_plus)^6, g_minus=-(a_minus)^6 under equal-c simplification",
            "implies": "FLRW determinant ratio may reduce to scale-factor powers only under stated gauge/symmetry limits",
            "closes": [],
        },
    ]
    blocker_implications = [
        {
            "blocker": "F_alpha",
            "source_status": "not supplied by M15",
            "reason": "M15 couples metric variations and field equations, but does not define L_minus_to_plus or D_alpha L",
            "next_needed": "derive cross-tetrad transport from later Janus geometry/geodesic sources or add it as an explicit axiom",
            "closed": False,
        },
        {
            "blocker": "D log B_4vol",
            "source_status": "definition supplied, cancellation not supplied",
            "reason": "M15 supplies sqrt(-g_other/-g_self), but not the covariant cross-derivative identities needed to cancel product-rule terms in R_plus/R_minus",
            "next_needed": "derive lapse/slice/cross-derivative identities or keep residual terms open",
            "closed": False,
        },
    ]
    rejection_rules = [
        "do not infer D_alpha L from delta g_plus = - delta g_minus",
        "do not treat FLRW g= -a^6 as a general non-FLRW B_4vol identity",
        "do not drop D log B_4vol product-rule terms after citing M15",
        "do not use M15 determinant factors as Q_cross optical normalization",
    ]
    return {
        "description": "P0 audit of what M15 supplies for the F_alpha and D log B_4vol blockers.",
        "status": "source-implications-open",
        "m15_checked": True,
        "b4vol_definition_source_anchored": True,
        "f_alpha_source_derived": False,
        "dlogb_cancellation_source_derived": False,
        "r_plus_closed": False,
        "r_minus_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "source_anchors": source_anchors,
        "blocker_implications": blocker_implications,
        "rejection_rules": rejection_rules,
        "verdict": (
            "M15 validates the B_4vol field-equation factor but does not close the "
            "transport problem. F_alpha and D log B_4vol cancellation remain open."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 M15 Source Identity Implications",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"M15 checked: {payload['m15_checked']}",
        f"B_4vol definition source anchored: {payload['b4vol_definition_source_anchored']}",
        f"F_alpha source-derived: {payload['f_alpha_source_derived']}",
        f"DlogB cancellation source-derived: {payload['dlogb_cancellation_source_derived']}",
        f"R_plus closed: {payload['r_plus_closed']}",
        f"R_minus closed: {payload['r_minus_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Source Anchors",
        "",
    ]
    for row in payload["source_anchors"]:
        lines.append(f"- {row['anchor']}: `{row['content']}`")
        lines.append(f"  - implies: {row['implies']}")
        lines.append(f"  - closes: {', '.join(row['closes']) if row['closes'] else 'none'}")
    lines.extend(["", "## Blocker Implications", ""])
    for row in payload["blocker_implications"]:
        lines.append(f"- {row['blocker']}: {row['source_status']}")
        lines.append(f"  - reason: {row['reason']}")
        lines.append(f"  - next needed: {row['next_needed']}")
        lines.append(f"  - closed: {row['closed']}")
    lines.extend(["", "## Rejection Rules", ""])
    lines.extend(f"- {item}" for item in payload["rejection_rules"])
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
