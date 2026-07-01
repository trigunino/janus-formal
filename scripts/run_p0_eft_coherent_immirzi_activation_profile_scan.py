from __future__ import annotations

from pathlib import Path
import json
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.run_p0_eft_coherent_primordial_immirzi_planck_gate import (
    SOURCE_PATH,
    delta_i,
    set_coherent_immirzi,
    build_fork,
    run_cobaya,
    reference_chi2,
)


REPORT_PATH = Path("outputs/reports/p0_eft_coherent_immirzi_activation_profile_scan.md")
JSON_PATH = Path("outputs/reports/p0_eft_coherent_immirzi_activation_profile_scan.json")
CSV_PATH = Path("outputs/reports/p0_eft_coherent_immirzi_activation_profile_scan.csv")

PROFILES = [
    {"label": "very_early_sharp", "a_center": 1.0e-4, "width": 5.0e-5},
    {"label": "early_adiabatic", "a_center": 2.5e-4, "width": 1.5e-4},
    {"label": "mid_adiabatic", "a_center": 5.0e-4, "width": 2.5e-4},
    {"label": "pre_drag_adiabatic", "a_center": 8.0e-4, "width": 4.0e-4},
]


def replace_primordial_profile(text: str, a_center: float, width: float) -> str:
    text = re.sub(
        r"(real\(dl\), parameter :: a_drag = )[-+0-9.eE]+_dl",
        rf"\g<1>{a_center:.16e}_dl",
        text,
    )
    text = re.sub(
        r"(real\(dl\), parameter :: width = )[-+0-9.eE]+_dl",
        rf"\g<1>{width:.16e}_dl",
        text,
        count=1,
    )
    return text


def set_profile(a_center: float, width: float) -> None:
    text = SOURCE_PATH.read_text(encoding="utf-8")
    SOURCE_PATH.write_text(replace_primordial_profile(text, a_center, width), encoding="utf-8")


def build_payload(execute: bool = True) -> dict:
    value = delta_i()
    ref = reference_chi2()
    if not execute:
        return {
            "description": "Activation profile scan for coherent Immirzi stress tensor.",
            "status": "coherent-immirzi-activation-profile-scan-dry",
            "profiles": PROFILES,
            "full_cosmology_prediction_ready_no_fit": False,
        }
    original = SOURCE_PATH.read_text(encoding="utf-8")
    rows = []
    try:
        for profile in PROFILES:
            SOURCE_PATH.write_text(original, encoding="utf-8")
            set_profile(profile["a_center"], profile["width"])
            set_coherent_immirzi(value)
            build_code = build_fork()
            result = run_cobaya() if build_code == 0 else {"returncode": build_code, "chi2_CMB": None}
            deltas = {
                f"delta_{key}": result[key] - ref[key]
                for key in ref
                if result.get(key) is not None
            }
            rows.append({**profile, "c_coherent_immirzi": value, "build_returncode": build_code, **result, **deltas})
    finally:
        SOURCE_PATH.write_text(original, encoding="utf-8")
        build_fork()
    valid = [row for row in rows if row.get("delta_chi2_CMB") is not None]
    best = min(valid, key=lambda row: row["delta_chi2_CMB"]) if valid else None
    return {
        "description": "Activation profile scan for coherent Immirzi stress tensor.",
        "status": "coherent-immirzi-activation-profile-scan-run",
        "profiles": PROFILES,
        "rows": rows,
        "best": best,
        "planck_delta_accepted": bool(best and best["delta_chi2_CMB"] < 0.0),
        "full_cosmology_prediction_ready_no_fit": False,
        "next_required": "If all profiles fail, the amplitude/source form is structurally incompatible with Planck high-l.",
    }


def render_markdown(payload: dict) -> str:
    best = payload.get("best") or {}
    lines = [
        "# P0 EFT Coherent Immirzi Activation Profile Scan",
        "",
        payload["description"],
        "",
        f"Status: `{payload['status']}`",
        f"Best: `{best.get('label')}`",
        f"Best delta chi2 CMB: `{best.get('delta_chi2_CMB')}`",
        f"Planck delta accepted: `{payload.get('planck_delta_accepted', False)}`",
        "",
        "| profile | a_center | width | delta CMB | delta highl | delta lensing |",
        "|---|---:|---:|---:|---:|---:|",
    ]
    for row in payload.get("rows", []):
        lines.append(
            f"| {row['label']} | {row['a_center']} | {row['width']} | "
            f"{row.get('delta_chi2_CMB')} | {row.get('delta_chi2_highl')} | {row.get('delta_chi2_lensing')} |"
        )
    return "\n".join(lines) + "\n"


def write_reports(execute: bool = True) -> dict:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload(execute=execute)
    headers = ["label", "a_center", "width", "delta_chi2_CMB", "delta_chi2_highl", "delta_chi2_lensing", "chi2_CMB", "returncode"]
    CSV_PATH.write_text(
        "\n".join([",".join(headers)] + [",".join(str(row.get(h, "")) for h in headers) for row in payload.get("rows", [])]) + "\n",
        encoding="utf-8",
    )
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")
    print(f"Wrote {CSV_PATH}")


if __name__ == "__main__":
    main()
