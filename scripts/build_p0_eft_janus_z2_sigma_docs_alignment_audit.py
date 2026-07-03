from __future__ import annotations

import json
from pathlib import Path


README = Path("README.md")
TODO = Path("TODO.md")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_docs_alignment_audit.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_docs_alignment_audit.json")

FORBIDDEN_SNIPPETS = [
    "janus_z4_master_equation_path = Active",
    "## Active CMB/Z4",
    "Status: new upstream track",
    "next viable direction is one upstream generator `U_Z4`",
    "physical Janus/Z4 verdict",
]


def _combined_text() -> str:
    return README.read_text(encoding="utf-8") + "\n" + TODO.read_text(encoding="utf-8")


def build_payload() -> dict:
    text = _combined_text()
    hits = [snippet for snippet in FORBIDDEN_SNIPPETS if snippet in text]
    required = {
        "active_geometry_core_declared": "active_geometry_core = Z2_tunnel_Sigma" in text,
        "legacy_z4_archived_declared": "legacy_z4_modules_archived = True" in text,
        "active_audit_declared": "P0EFTJanusZ2SigmaPureMathClosureAuditGate" in text,
        "facade_audit_declared": "active facade audit" in text,
    }
    return {
        "status": "janus-z2-sigma-docs-alignment-audit",
        "forbidden_active_z4_snippets": hits,
        "required_markers": required,
        "docs_aligned_to_z2_sigma": not hits and all(required.values()),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join([
            "# Janus Z2/Sigma Docs Alignment Audit",
            "",
            f"Docs aligned to Z2/Sigma: `{payload['docs_aligned_to_z2_sigma']}`",
            f"Forbidden active Z4 snippets: `{payload['forbidden_active_z4_snippets']}`",
        ]),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
