from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.janus_lab.z2_so3_throat_embedding import so3_throat_embedding_manifest


ACTIVE_PATH = Path("outputs/active_z2_sigma/so3_throat_embedding_manifest.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_so3_throat_embedding_manifest.md")


def build_payload() -> dict:
    return so3_throat_embedding_manifest()


def write_outputs() -> dict:
    payload = build_payload()
    ACTIVE_PATH.parent.mkdir(parents=True, exist_ok=True)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    ACTIVE_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 SO(3) Throat Embedding Manifest",
        "",
        f"Embedding skeleton ready: `{payload['active_embedding_skeleton_ready']}`",
        f"SO(3) reduced Bianchi ready: `{payload['SO3_reduced_bianchi_ready']}`",
        f"Metric functions ready: `{payload['metric_functions_ready']}`",
        f"DeltaK ready: `{payload['DeltaK_s_tau_ready']}`",
        f"R_Sigma certificate ready: `{payload['R_Sigma_solution_certificate_ready']}`",
        "",
        "## Non-Claims",
    ]
    lines.extend(f"- `{item}`" for item in payload["non_claims"])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_outputs(), indent=2))
