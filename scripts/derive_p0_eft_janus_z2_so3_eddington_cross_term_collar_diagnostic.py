from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.janus_lab.z2_so3_eddington_cross_term import (
    eddington_cross_term_collar_diagnostic,
)


JSON_PATH = Path("outputs/active_z2_sigma/so3_eddington_cross_term_collar_diagnostic.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_so3_eddington_cross_term_collar_diagnostic.md")


def build_payload() -> dict:
    return eddington_cross_term_collar_diagnostic()


def write_outputs() -> dict:
    payload = build_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 SO(3) Eddington Cross-Term Collar Diagnostic",
        "",
        f"Bulk TR block regular at R_s: `{payload['bulk_TR_block_regular_at_Rs']}`",
        f"R=const throat induced metric null: `{payload['R_const_throat_induced_metric_null']}`",
        f"Current regular Sigma h/K compatible: `{payload['current_regular_sigma_hK_formalism_compatible']}`",
        "",
        "## Interpretation",
        "",
        payload["interpretation"],
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_outputs(), indent=2))
