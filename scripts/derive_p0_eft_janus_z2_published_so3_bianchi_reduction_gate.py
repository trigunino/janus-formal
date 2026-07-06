from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.derive_p0_eft_janus_z2_published_interaction_slots_gate import (
    build_payload as interaction_slots,
)
from src.janus_lab.z2_published_so3_bianchi_reduction import (
    published_so3_bianchi_reduction_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_published_so3_bianchi_reduction_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_published_so3_bianchi_reduction_gate.json")


def build_payload() -> dict:
    slots = interaction_slots()
    so3 = published_so3_bianchi_reduction_payload()
    gate_passed = (
        slots["gate_passed"]
        and so3["same_sector_attraction_ready"]
        and so3["opposite_sector_repulsion_ready"]
        and so3["tov_newtonian_bianchi_asymptotic_ready"]
    )
    return {
        "status": "janus-z2-published-so3-bianchi-reduction-gate",
        "active_core": so3["active_core"],
        "source": so3["source"],
        "reference_pages": so3["reference_pages"],
        "interaction_slots_ready": slots["gate_passed"],
        "reduction_type": so3["reduction_type"],
        "interaction_terms": so3["interaction_terms"],
        "stationary_so3_reduced_bianchi_ready": so3["stationary_so3_reduced_bianchi_ready"],
        "generic_tensor_bianchi_ready": so3["generic_tensor_bianchi_ready"],
        "sigma_transport_ready": so3["sigma_transport_ready"],
        "sigma_source_available": so3["sigma_source_available"],
        "active_embedding_ready": so3["active_embedding_ready"],
        "allowed_use": so3["allowed_use"],
        "non_claims": so3["non_claims"],
        "next_required": so3["next_required"],
        "gate_passed": gate_passed,
        "full_no_fit_prediction_ready": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Published SO(3) Bianchi Reduction Gate",
        "",
        f"Interaction slots ready: `{payload['interaction_slots_ready']}`",
        f"Reduction type: `{payload['reduction_type']}`",
        f"Stationary SO(3) reduced Bianchi ready: `{payload['stationary_so3_reduced_bianchi_ready']}`",
        f"Generic tensor Bianchi ready: `{payload['generic_tensor_bianchi_ready']}`",
        f"Sigma transport ready: `{payload['sigma_transport_ready']}`",
        "",
        "## Interaction Terms",
        "",
        "| term | force sign | status |",
        "|---|---|---|",
    ]
    for name, row in payload["interaction_terms"].items():
        lines.append(f"| `{name}` | `{row['force_sign']}` | `{row['status']}` |")
    lines.extend(["", "## Allowed Use"])
    lines.extend(f"- `{item}`" for item in payload["allowed_use"])
    lines.extend(["", "## Non-Claims"])
    lines.extend(f"- `{item}`" for item in payload["non_claims"])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
