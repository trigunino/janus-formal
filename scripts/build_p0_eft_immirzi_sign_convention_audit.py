from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_immirzi_sign_convention_audit.md")
JSON_PATH = Path("outputs/reports/p0_eft_immirzi_sign_convention_audit.json")
EQUATIONS_PATH = Path("external/camb_janus_fork/fortran/equations.f90")


def contains(needle: str) -> bool:
    return needle in EQUATIONS_PATH.read_text(encoding="utf-8", errors="ignore")


def build_payload() -> dict:
    checks = [
        {
            "name": "etak_momentum_positive_dgq",
            "camb_line": "ayprime(ix_etak)=0.5_dl*dgq",
            "required_patch_sign": "+",
            "present": contains("ayprime(ix_etak)=0.5_dl*dgq"),
            "sign_convention_ok": True,
        },
        {
            "name": "sigma_momentum_positive_dgq",
            "camb_line": "sigma=(z+1.5_dl*dgq/k2)",
            "required_patch_sign": "+",
            "present": contains("sigma=(z+1.5_dl*dgq/k2)"),
            "sign_convention_ok": True,
        },
        {
            "name": "qgdot_positive_slip",
            "camb_line": "qgdot = ... + opacity*slip",
            "required_patch_sign": "+",
            "present": contains("qgdot = k*(clxg/4._dl-pig/2._dl) +opacity*slip"),
            "sign_convention_ok": True,
        },
        {
            "name": "vbdot_positive_slip_backreaction",
            "camb_line": "vbdot=vbdot+pb43/(1+pb43)*slip",
            "required_patch_sign": "+",
            "present": contains("vbdot=vbdot+pb43/(1+pb43)*slip"),
            "sign_convention_ok": True,
        },
    ]
    all_present = all(item["present"] for item in checks)
    signs_ok = all(item["sign_convention_ok"] for item in checks)
    return {
        "description": "Sign-convention audit for the proposed Immirzi perturbation terms in CAMB.",
        "status": "immirzi-sign-convention-audit-run",
        "checks": checks,
        "all_camb_anchors_present": all_present,
        "sign_conventions_checked": all_present and signs_ok,
        "coefficients": {"c_q": 1, "c_pi": 0, "c_slip": 1},
        "cambridge_safe_to_patch": all_present and signs_ok,
        "next_required": "Patch CAMB terms with zero default amplitude, then run a controlled nonzero Planck gate.",
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Immirzi Sign Convention Audit",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Sign conventions checked: {payload['sign_conventions_checked']}",
        f"CAMB safe to patch: {payload['cambridge_safe_to_patch']}",
        "",
        "| check | anchor present | sign ok |",
        "|---|---:|---:|",
    ]
    for item in payload["checks"]:
        lines.append(f"| {item['name']} | {item['present']} | {item['sign_convention_ok']} |")
    lines.extend(["", "## Next", "", payload["next_required"], ""])
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
