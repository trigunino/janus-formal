from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/bianchi_flrw_lapse_volume_audit.md")
JSON_PATH = Path("outputs/reports/bianchi_flrw_lapse_volume_audit.json")


def build_payload() -> dict:
    metric_setup = [
        "ds_s^2=-N_s(t)^2 dt^2 + a_s(t)^2 gamma_ij dx^i dx^j",
        "sqrt(-g_s)=N_s a_s^3 sqrt(gamma)",
        "det4_metric_plus=sqrt(-g_minus)/sqrt(-g_plus)",
        "det4_metric_plus=(N_minus a_minus^3)/(N_plus a_plus^3)",
        "if spatial gamma differs, multiply by sqrt(det(gamma_minus)/det(gamma_plus))",
        "det4_metric_minus=(N_plus a_plus^3)/(N_minus a_minus^3)",
    ]
    gauge_cases = [
        {
            "case": "common_cosmic_time",
            "condition": "N_plus=N_minus=1",
            "det4_metric_plus": "(a_minus/a_plus)^3",
            "status": "volume determinant branch",
        },
        {
            "case": "sector_conformal_lapse_ratio",
            "condition": "N_minus/N_plus=a_minus/a_plus",
            "det4_metric_plus": "(a_minus/a_plus)^4",
            "status": "gauge-specific determinant branch",
        },
    ]
    guards = [
        "declare N_minus/N_plus before assigning a power to det4_metric_plus",
        "declare whether gamma_minus equals gamma_plus before dropping spatial determinant ratios",
        "do not identify det4_metric_plus with weight3_dust_plus",
        "weight3_dust_plus can remain cubic even when det4_metric_plus is quartic",
        "do not use either cubic or quartic scale ratio as a lensing amplitude",
        "Q_cross optical projection remains a separate derivation",
    ]
    return {
        "description": "FLRW lapse/volume audit for Janus determinant factors.",
        "status": "gauge-audit",
        "determinant_formula_closed": True,
        "physics_closed": False,
        "metric_setup": metric_setup,
        "gauge_cases": gauge_cases,
        "guards": guards,
        "verdict": (
            "The determinant factor is lapse times spatial volume. A quartic scale "
            "ratio is a gauge-specific determinant branch, not the dust volume "
            "weight and not a lensing amplitude."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Bianchi FLRW Lapse/Volume Audit",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Determinant formula closed: {payload['determinant_formula_closed']}",
        f"Physics closed: {payload['physics_closed']}",
        "",
        "## Metric Setup",
        "",
    ]
    lines.extend(f"- `{item}`" for item in payload["metric_setup"])
    lines.extend(["", "## Gauge Cases", ""])
    lines.extend(["| case | condition | det4_metric_plus | status |", "|---|---|---|---|"])
    for row in payload["gauge_cases"]:
        lines.append(
            f"| {row['case']} | `{row['condition']}` | "
            f"`{row['det4_metric_plus']}` | {row['status']} |"
        )
    lines.extend(["", "## Guards", ""])
    lines.extend(f"- {item}" for item in payload["guards"])
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
