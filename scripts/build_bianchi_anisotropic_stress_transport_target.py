from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/bianchi_anisotropic_stress_transport_target.md")
JSON_PATH = Path("outputs/reports/bianchi_anisotropic_stress_transport_target.json")


def build_payload() -> dict:
    tensor_form = [
        "T_s^{mu nu}=(rho_s+p_s)u_s^mu u_s^nu+p_s g_s^{mu nu}+Pi_s^{mu nu}",
        "Pi_s^{mu nu} u_{s nu}=0",
        "g_{s mu nu} Pi_s^{mu nu}=0",
    ]
    transport_targets = [
        "K_plus^{mu nu}=Transport_{- to +}[T_minus^{ab}]",
        "K_minus^{mu nu}=Transport_{+ to -}[T_plus^{ab}]",
        "D_plus_nu(T_plus^{mu nu}+B_plus K_plus^{mu nu})=0",
        "D_minus_nu(B_minus K_minus^{mu nu}+T_minus^{mu nu})=0",
    ]
    required_maps = [
        "sector tetrad or frame map",
        "metric raising/lowering convention after transport",
        "velocity/covector map for u_minus into positive tangent space",
        "spatial projector map for Pi_minus",
        "connection-difference terms in both divergences",
    ]
    forbidden_reductions = [
        "replace Pi_s^{mu nu} by scalar rho_s",
        "reuse perfect-fluid w_cross branch when Pi_s^{mu nu} is nonzero",
        "merge anisotropic stress into Q_cross",
        "claim shear/lensing normalization before tensor contraction is derived",
    ]
    return {
        "description": "Target for anisotropic-stress transport in Bianchi-compatible Janus sources.",
        "status": "tensor-target",
        "physics_closed": False,
        "tensor_form": tensor_form,
        "transport_targets": transport_targets,
        "required_maps": required_maps,
        "forbidden_reductions": forbidden_reductions,
        "verdict": (
            "Anisotropic stress must be transported as a tensor. The FLRW dust and "
            "perfect-fluid scalar branches are not valid replacements when Pi is nonzero."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Bianchi Anisotropic-Stress Transport Target",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Physics closed: {payload['physics_closed']}",
        "",
        "## Tensor Form",
        "",
    ]
    lines.extend(f"- `{item}`" for item in payload["tensor_form"])
    lines.extend(["", "## Transport Targets", ""])
    lines.extend(f"- `{item}`" for item in payload["transport_targets"])
    lines.extend(["", "## Required Maps", ""])
    lines.extend(f"- {item}" for item in payload["required_maps"])
    lines.extend(["", "## Forbidden Reductions", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_reductions"])
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    return "\n".join(lines)


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(render_markdown(payload), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
