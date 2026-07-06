from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.janus_lab.z2_so3_signed_schwarzschild import (
    signed_schwarzschild_metric_diagnostic,
)


JSON_PATH = Path("outputs/active_z2_sigma/so3_signed_schwarzschild_metric_diagnostic.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_so3_signed_schwarzschild_metric_diagnostic.md")


def build_payload() -> dict:
    return signed_schwarzschild_metric_diagnostic()


def write_outputs() -> dict:
    payload = build_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 SO(3) Signed Schwarzschild Metric Diagnostic",
        "",
        f"Formula: `{payload['formula']}`",
        f"Attractive block degenerate at R_s: `{payload['attractive_block_degenerate_at_Rs']}`",
        f"Repulsive block regular at R_s: `{payload['repulsive_block_regular_at_Rs']}`",
        f"Thin-shell K formula ready at R_s: `{payload['thin_shell_K_formula_ready_at_Rs']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_outputs(), indent=2))
