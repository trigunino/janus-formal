from __future__ import annotations

import json
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from janus_lab import published_janus_extended2026_background


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_extended2026_observational_claim_map.json"
REPORT_PATH = REPORTS / "p0_eft_janus_extended2026_observational_claim_map.md"


def build_payload() -> dict:
    background = published_janus_extended2026_background()
    claims = [
        {
            "source_id": "M18",
            "claim_id": "m18_sn_proxy_shape",
            "statement": "The exact Janus expansion plus SN magnitude-redshift proxy fits Type Ia supernovae with q0 as the shape parameter.",
            "anchor": "M18 Eqs. 5, 6, 10, 13, 20-21",
            "class": "direct_observational_claim",
            "status": "strictly_reproducible",
            "strictly_executable": True,
            "notes": "Published plus-branch shape and SN proxy are executable with profiled additive offset.",
        },
        {
            "source_id": "M18",
            "claim_id": "m18_q0_value",
            "statement": "Best-fit Janus SN shape parameter is q0 = -0.087 +/- 0.015.",
            "anchor": "M18 Eq. 6",
            "class": "direct_observational_claim",
            "status": "strictly_reproducible",
            "strictly_executable": True,
            "notes": "Published q0 anchor is directly encoded in the strict active background object.",
        },
        {
            "source_id": "M18",
            "claim_id": "m18_open_distance_basis",
            "statement": "Open-marker distance relations can be written explicitly from the exact Janus branch.",
            "anchor": "M18 Eqs. 14-17, 20-21",
            "class": "geometric_observational_basis",
            "status": "strictly_reproducible",
            "strictly_executable": True,
            "notes": "Distance basis is executable, but not yet a native BAO prediction.",
        },
        {
            "source_id": "M18",
            "claim_id": "m18_bao_native_prediction",
            "statement": "BAO can be predicted natively from the same Janus exact branch.",
            "anchor": "M18 discussion around Eqs. 14-17",
            "class": "derived_observational_extension",
            "status": "blocked_by_missing_native_ruler",
            "strictly_executable": False,
            "notes": "The active papers do not close a native ruler/calibration contract.",
        },
        {
            "source_id": "M30",
            "claim_id": "m30_2024_observational_reuse",
            "statement": "The 2024 paper reuses the Janus acceleration/SN branch as an observational anchor.",
            "anchor": "EPJC 2024 observational discussion plus M18 reuse",
            "class": "paper_reuse_claim",
            "status": "strictly_reproducible_via_m18_layer",
            "strictly_executable": True,
            "notes": "This is executable only through the already-published M18 branch, not from a new 2024 standalone observable derivation.",
        },
        {
            "source_id": "X2026-expansion-desi",
            "claim_id": "x2026_desi_consistency",
            "statement": "The Janus exact expansion law is consistent with DESI-era evidence for stronger past acceleration.",
            "anchor": "X2026-expansion-desi abstract and Eqs. 27-29",
            "class": "source_level_observational_claim",
            "status": "affirmed_but_not_natively_executable",
            "strictly_executable": False,
            "notes": "The source claim is indexed and anchored, but a native DESI observable contract is not closed by the active texts.",
        },
        {
            "source_id": "X2026-variable-constants",
            "claim_id": "x2026_variable_constants_gauge",
            "statement": "The variable-constants regime defines a published gauge set for early-universe scalings.",
            "anchor": "X2026-variable-constants Eq. 40",
            "class": "published_formula_layer",
            "status": "strictly_reproducible",
            "strictly_executable": True,
            "notes": "Eq. 40 exponents are encoded exactly as published.",
        },
        {
            "source_id": "X2026-variable-constants",
            "claim_id": "x2026_bao_ruler_clue",
            "statement": "The variable-constants regime supplies a native BAO ruler prediction.",
            "anchor": "X2026-variable-constants discussion around Eq. 40",
            "class": "derived_observational_extension",
            "status": "not_derived_by_active_text",
            "strictly_executable": False,
            "notes": "The active texts provide a clue for ruler scaling, not a closed observable formula.",
        },
        {
            "source_id": "X2026-variable-constants",
            "claim_id": "x2026_cmb_path",
            "statement": "The variable-constants regime closes a native CMB observable path.",
            "anchor": "X2026-variable-constants broad discussion",
            "class": "derived_observational_extension",
            "status": "not_derived_by_active_text",
            "strictly_executable": False,
            "notes": "No strict CMB transfer/observable pipeline is published in the active source set.",
        },
    ]
    counts = Counter(item["status"] for item in claims)
    return {
        "status": "janus-extended2026-observational-claim-map",
        "source_policy": "strict_active_sources_only",
        "published_q0": background.q0,
        "published_h0_km_s_mpc": background.h0_km_s_mpc,
        "claims": claims,
        "counts_by_status": dict(counts),
        "strictly_reproducible_claim_count": sum(
            1 for item in claims if item["strictly_executable"]
        ),
        "non_executable_claim_count": sum(
            1 for item in claims if not item["strictly_executable"]
        ),
        "next_allowed_execution_scope": [
            "M18_SN_proxy_shape",
            "M18_q0_anchor",
            "M18_open_distance_basis",
            "X2026_variable_constants_eq40_gauge",
        ],
        "forbidden_scope_without_new_paper_level_derivation": [
            "native_BAO_ruler_validation",
            "DESI_native_endpoint_claim",
            "native_CMB_claim",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Extended2026 Observational Claim Map",
        "",
        f"Source policy: `{payload['source_policy']}`",
        f"Strictly reproducible claims: `{payload['strictly_reproducible_claim_count']}`",
        f"Non-executable claims: `{payload['non_executable_claim_count']}`",
        "",
        "## Claims",
        "",
        "| Source | Claim | Class | Status | Strict |",
        "|---|---|---|---|---|",
    ]
    for item in payload["claims"]:
        lines.append(
            f"| `{item['source_id']}` | {item['claim_id']} | `{item['class']}` | `{item['status']}` | `{item['strictly_executable']}` |"
        )
    lines.extend(
        [
            "",
            "## Allowed now",
            "",
            *[f"- `{item}`" for item in payload["next_allowed_execution_scope"]],
            "",
            "## Forbidden without new paper-level derivation",
            "",
            *[
                f"- `{item}`"
                for item in payload["forbidden_scope_without_new_paper_level_derivation"]
            ],
        ]
    )
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
