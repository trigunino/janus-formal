from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any


INPUT_PATH = Path("outputs/active_z2_sigma/published_exact_solution_scale_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_published_exact_solution_scale_frontier_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_published_exact_solution_scale_frontier_gate.json"
)
FORBIDDEN = ("fit", "planck", "lcdm", "bao", "z4", "demo")


def h_shape(u: float) -> float:
    if u <= 0.0:
        raise ValueError("u must be positive")
    return math.sinh(2.0 * u) / math.cosh(u) ** 4


def alpha_from_h0(u0: float, h0_s_inv: float) -> float:
    if h0_s_inv <= 0.0:
        raise ValueError("H0 must be positive")
    return h_shape(u0) / h0_s_inv


def _read(path: Path) -> dict[str, Any] | None:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else None


def _bad_provenance(value: Any) -> bool:
    text = str(value or "").strip().lower()
    return not text or any(token in text for token in FORBIDDEN)


def build_payload(*, input_path: Path = INPUT_PATH) -> dict[str, Any]:
    data = _read(input_path)
    alpha_seconds = None
    errors: list[str] = []
    if data is not None:
        if data.get("active_core") != "Z2_tunnel_Sigma":
            errors.append("active_core_must_be_Z2_tunnel_Sigma")
        if _bad_provenance(data.get("scale_provenance")):
            errors.append("scale_provenance_missing_or_forbidden")
        if "alpha_seconds" in data:
            alpha_seconds = float(data["alpha_seconds"])
            if alpha_seconds <= 0.0:
                errors.append("alpha_seconds_must_be_positive")
        elif "u0" in data and "H0_s_inv" in data:
            alpha_seconds = alpha_from_h0(float(data["u0"]), float(data["H0_s_inv"]))
        else:
            errors.append("need_alpha_seconds_or_u0_plus_H0_s_inv")
        for key in [
            "observational_fit_used",
            "compressed_planck_lcdm_background_used",
            "archived_z4_reuse_used",
        ]:
            if data.get(key) is True:
                errors.append(f"forbidden_flag:{key}")
    else:
        errors.append("missing_published_exact_solution_scale_inputs")

    ready = alpha_seconds is not None and not errors
    return {
        "status": "janus-z2-published-exact-solution-scale-frontier-gate",
        "active_core": "Z2_tunnel_Sigma",
        "published_anchor": "D'Agostini-Petit exact expansion: a(u)=alpha*cosh(u)^2; t(u)=alpha/2*(1+sinh(2u)/2+u).",
        "derived_relation": "H(u)=sinh(2u)/(alpha*cosh(u)^4); alpha=h_shape(u0)/H0.",
        "shape_closed": True,
        "dimensionless_u0_or_q0_can_shape_distances": True,
        "absolute_scale_requires_alpha_or_H0_or_clock": True,
        "input_exists": data is not None,
        "alpha_seconds": alpha_seconds,
        "scale_ready": ready,
        "validation_errors": errors,
        "how_published_model_handles_scale": (
            "The published SN route uses the exact dimensionless shape plus a "
            "distance-modulus offset/free parameter. That is legitimate for an "
            "observational fit, but it is not a no-rustine derivation of alpha."
        ),
        "impact_on_rho_plus0_abs": (
            "Without alpha/H0 or an equivalent global energy state, the exact "
            "solution cannot supply an absolute density normalization."
        ),
        "gate_passed": ready,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Published Exact Solution Scale Frontier Gate",
        "",
        f"Shape closed: `{payload['shape_closed']}`",
        f"Scale ready: `{payload['scale_ready']}`",
        f"Derived relation: `{payload['derived_relation']}`",
        "",
        payload["how_published_model_handles_scale"],
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
