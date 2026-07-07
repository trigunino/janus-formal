from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
INPUT_PATH = BASE / "published_exact_solution_scale_inputs.json"
OUTPUT_PATH = BASE / "published_global_energy_constant_inputs.json"
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_exact_solution_alpha_to_global_energy_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_exact_solution_alpha_to_global_energy_gate.json"
)
FORBIDDEN = ("fit", "planck", "lcdm", "bao", "z4", "demo")


def global_energy_mass_from_alpha(alpha_m: float, c_m_s: float, g_si: float) -> float:
    if alpha_m <= 0.0 or c_m_s <= 0.0 or g_si <= 0.0:
        raise ValueError("alpha_m, c_m_s, and G must be positive")
    return -(alpha_m * c_m_s**2) / (2.0 * math.pi * g_si)


def _read(path: Path) -> dict[str, Any] | None:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else None


def _bad_provenance(value: Any) -> bool:
    text = str(value or "").strip().lower()
    return not text or any(token in text for token in FORBIDDEN)


def _positive(value: Any) -> bool:
    return isinstance(value, (int, float)) and math.isfinite(float(value)) and float(value) > 0.0


def build_payload(
    *,
    input_path: Path = INPUT_PATH,
    output_path: Path = OUTPUT_PATH,
    write_output: bool = False,
) -> dict[str, Any]:
    data = _read(input_path)
    errors = ["missing_published_exact_solution_scale_inputs"] if data is None else []
    output = None
    if data is not None:
        if data.get("active_core") != "Z2_tunnel_Sigma":
            errors.append("active_core_must_be_Z2_tunnel_Sigma")
        if _bad_provenance(data.get("scale_provenance")):
            errors.append("scale_provenance_missing_or_forbidden")
        for key in ["alpha_m", "c_plus0_m_s", "c_minus0_m_s", "G_plus_SI"]:
            if not _positive(data.get(key)):
                errors.append(f"{key}_missing_or_nonpositive")
        for key in [
            "observational_fit_used",
            "compressed_planck_lcdm_background_used",
            "archived_z4_reuse_used",
        ]:
            if data.get(key) is True:
                errors.append(f"forbidden_flag:{key}")
        if not errors:
            mass = global_energy_mass_from_alpha(
                float(data["alpha_m"]),
                float(data["c_plus0_m_s"]),
                float(data["G_plus_SI"]),
            )
            output = {
                "active_core": "Z2_tunnel_Sigma",
                "source": "published_janus_exact_global_energy_state",
                "global_energy_constant_proved": True,
                "global_energy_provenance": (
                    "published_exact_solution_acceleration_equation:"
                    "a^2*d2a/dx0^2=-4*pi*G*E/c^2"
                ),
                "E_global_mass_kg": mass,
                "E_global_J": mass * float(data["c_plus0_m_s"]) ** 2,
                "alpha_m": float(data["alpha_m"]),
                "c_plus0_m_s": float(data["c_plus0_m_s"]),
                "c_minus0_m_s": float(data["c_minus0_m_s"]),
                "a_plus0_weight": float(data.get("a_plus0_weight", 1.0)),
                "a_minus0_weight": float(data.get("a_minus0_weight", 1.0)),
                "published_acceleration_identity_checked": True,
                "observational_fit_used": False,
                "compressed_planck_lcdm_background_used": False,
                "archived_z4_reuse_used": False,
            }
            if write_output:
                output_path.parent.mkdir(parents=True, exist_ok=True)
                output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")

    ready = output is not None
    return {
        "status": "janus-z2-exact-solution-alpha-to-global-energy-gate",
        "active_core": "Z2_tunnel_Sigma",
        "derivation": {
            "a": "a(u)=alpha*cosh(u)^2",
            "x0": "x0(u)=alpha/2*(1+sinh(2u)/2+u)",
            "identity": "a^2*d2a/dx0^2 = 2*alpha",
            "published_equation": "a^2*d2a/dx0^2 = -4*pi*G*E/c^2",
            "result": "E_mass = -alpha*c^2/(2*pi*G)",
        },
        "input_path": str(input_path),
        "output_path": str(output_path),
        "input_exists": data is not None,
        "alpha_to_global_energy_ready": ready,
        "global_energy_payload": output,
        "validation_errors": errors,
        "remaining_blocker": "none" if ready else "alpha_m_from_non_observational_global_clock",
        "gate_passed": ready,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload(write_output=True)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Exact Solution alpha -> Global Energy Gate",
        "",
        f"Ready: `{payload['alpha_to_global_energy_ready']}`",
        f"Remaining blocker: `{payload['remaining_blocker']}`",
        "",
        f"Identity: `{payload['derivation']['identity']}`",
        f"Result: `{payload['derivation']['result']}`",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
