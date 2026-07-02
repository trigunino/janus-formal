from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_local_cosmology_profiling_readiness_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_local_cosmology_profiling_readiness_gate.json")
GR_HANDSHAKE_JSON = Path("outputs/reports/p0_eft_janus_z4_regenerative_gr_handshake_gate.json")
CACHE_JSON = Path("outputs/reports/p0_eft_janus_z4_regenerative_cache_invalidation_gate.json")
REPLAY_JSON = Path("outputs/reports/p0_eft_janus_z4_regenerative_frozen_candidate_replay_gate.json")
Z4_DELTA_JSON = Path("outputs/reports/p0_eft_janus_z4_regenerative_z4_delta_per_cosmology_gate.json")
SOURCE_JSON = Path("outputs/reports/p0_eft_janus_z4_regenerative_source_level_delta_gate.json")


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def build_payload() -> dict:
    gr = _load(GR_HANDSHAKE_JSON)
    cache = _load(CACHE_JSON)
    replay = _load(REPLAY_JSON)
    z4 = _load(Z4_DELTA_JSON)
    source = _load(SOURCE_JSON)
    ready = bool(
        gr.get("regenerative_gr_handshake_passed")
        and cache.get("gate_passed")
        and replay.get("regenerative_frozen_candidate_replay_passed")
        and z4.get("effective_gate_passed")
        and source.get("strict_source_level_gate_passed")
    )
    return {
        "status": "janus-z4-local-cosmology-profiling-readiness-gate",
        "regenerative_GR_handshake_passed": bool(gr.get("regenerative_gr_handshake_passed")),
        "cache_invalidation_passed": bool(cache.get("gate_passed")),
        "frozen_candidate_replay_passed": bool(replay.get("regenerative_frozen_candidate_replay_passed")),
        "effective_z4_spectrum_deltas_regenerated_per_cosmology": bool(z4.get("effective_gate_passed")),
        "source_level_z4_deltas_regenerated_per_cosmology": bool(source.get("strict_source_level_gate_passed")),
        "same_nonoverlap_accounting_required": True,
        "lambda_frozen_for_first_profile": True,
        "local_cosmology_profiling_allowed": ready,
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
        "blocked_reason": None
        if ready
        else "source-level Z4 delta regeneration is not closed; effective spectral deltas alone are insufficient for cosmology profiling",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Local Cosmology Profiling Readiness Gate",
        "",
        f"Local cosmology profiling allowed: `{payload['local_cosmology_profiling_allowed']}`",
        f"Source-level Z4 deltas regenerated: `{payload['source_level_z4_deltas_regenerated_per_cosmology']}`",
        f"Blocked reason: `{payload['blocked_reason']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
