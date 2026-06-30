from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/qdet_metric_volume_target.md")
JSON_PATH = Path("outputs/reports/qdet_metric_volume_target.json")


def build_payload() -> dict:
    branches = [
        {
            "branch": "positive_effective",
            "density_measure": "rho_minus_eff already expressed in the positive-sector source volume",
            "q_det": "1 by convention; determinant factor absorbed into rho_minus_eff",
            "status": "admissible-diagnostic",
            "allowed_use": "weak-field source diagnostics only",
            "not_allowed": "final tensor-lensing normalization or S8_eff claim",
        },
        {
            "branch": "negative_proper",
            "density_measure": "rho_minus_proper in the negative-sector metric volume",
            "q_det": "sqrt(-g_minus / -g_plus) as a formal metric-volume bridge",
            "status": "admissible-derivation-target",
            "allowed_use": "symbolic branch map once the volume convention is derived",
            "not_allowed": "numerical insertion before the metric-volume map is proven",
        },
        {
            "branch": "flrw_raw_forbidden",
            "density_measure": "raw FLRW scale-factor ratio used as an optical amplitude",
            "q_det": "(a_minus / a_plus)^4 without a volume/gauge derivation",
            "status": "forbidden",
            "allowed_use": "none",
            "not_allowed": "stacking raw FLRW determinant factors into lensing predictions",
        },
    ]
    missing_for_tensor_lensing = [
        "derive the common positive optical volume used by negative-sector sources",
        "state whether rho_minus input is positive-effective or negative-proper",
        "prove the determinant/lapse gauge relation before using FLRW scale ratios",
        "derive the cross-sector stress projection along positive null rays",
        "close the coupled tensor source normalization without fitting Q_det",
    ]
    return {
        "description": "Q_det metric-volume mapping target for Janus lensing branches.",
        "branches": branches,
        "missing_for_tensor_lensing": missing_for_tensor_lensing,
        "closes_tensor_lensing": False,
        "verdict": (
            "positive_effective is the current diagnostic convention; negative_proper "
            "is only a derivation target; raw FLRW determinant insertion is forbidden. "
            "This report does not close the tensor-lensing physics."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Q_det Metric-Volume Mapping Target",
        "",
        payload["description"],
        "",
        "| branch | density measure | Q_det | status | allowed use | not allowed |",
        "|---|---|---|---|---|---|",
    ]
    for row in payload["branches"]:
        lines.append(
            f"| {row['branch']} | {row['density_measure']} | {row['q_det']} | "
            f"{row['status']} | {row['allowed_use']} | {row['not_allowed']} |"
        )
    lines.extend(["", "## Missing For Tensor Lensing", ""])
    lines.extend(f"- {item}" for item in payload["missing_for_tensor_lensing"])
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
