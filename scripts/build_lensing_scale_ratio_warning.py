from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/lensing_scale_ratio_warning.md")
JSON_PATH = Path("outputs/reports/lensing_scale_ratio_warning.json")


def main() -> None:
    scale_ratio = 1.0 / 100.0
    q_det_raw = scale_ratio**4
    q_cross_raw = scale_ratio**2
    stacked = q_det_raw * q_cross_raw
    payload = {
        "description": "Why M20 a_-/a_+ ~= 1/100 cannot be used directly as a lensing amplitude.",
        "scale_ratio": scale_ratio,
        "raw_q_det": q_det_raw,
        "raw_q_cross": q_cross_raw,
        "raw_stacked_weight": stacked,
        "verdict": (
            "The M20 scale ratio is a CMB/length-scale clue, not a verified optical "
            "determinant or projection amplitude. Direct insertion would suppress the "
            "negative-sector lensing source by 1e-8 or 1e-12 depending on stacking, "
            "which conflicts with the M30 Newtonian determinant-ratio ~= 1 limit and "
            "with Janus negative-lensing claims unless a full gauge/volume derivation is supplied."
        ),
    }
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")

    lines = [
        "# Lensing Scale-Ratio Warning",
        "",
        payload["description"],
        "",
        "| quantity | value | meaning |",
        "|---|---:|---|",
        f"| `a_-/a_+` | {scale_ratio:.3g} | M20 CMB-imprint scale ratio |",
        f"| raw `Q_det=(a_-/a_+)^4` | {q_det_raw:.3g} | determinant path only |",
        f"| raw `Q_cross=(a_-/a_+)^2` | {q_cross_raw:.3g} | lapse/projection path only |",
        f"| raw `W_-=Q_det Q_cross` | {stacked:.3g} | forbidden stacked shortcut |",
        "",
        f"Verdict: {payload['verdict']}",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
