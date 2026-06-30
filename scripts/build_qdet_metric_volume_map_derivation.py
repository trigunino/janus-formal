from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/qdet_metric_volume_map_derivation.md")
JSON_PATH = Path("outputs/reports/qdet_metric_volume_map_derivation.json")


def build_payload() -> dict:
    definitions = {
        "qdet_4volume_ratio": (
            "sqrt(-g_minus) / sqrt(-g_plus); in FLRW coordinates "
            "(N_minus a_minus^3 sqrt(gamma_minus)) / "
            "(N_plus a_plus^3 sqrt(gamma_plus))"
        ),
        "qdet_dust_volume_ratio": (
            "sqrt(h_minus) / sqrt(h_plus); in FLRW slices "
            "(a_minus^3 sqrt(gamma_minus)) / (a_plus^3 sqrt(gamma_plus))"
        ),
        "rho_minus_eff_plus_measure": (
            "rho_minus_eff_plus = qdet_metric_volume_factor rho_minus_proper"
        ),
    }
    distinctions = [
        {
            "name": "qdet_4volume_ratio",
            "role": "field-equation metric-volume bridge",
            "includes_lapse": True,
            "is_optical_lensing_amplitude": False,
            "is_qcross": False,
        },
        {
            "name": "qdet_dust_volume_ratio",
            "role": "three-volume dust measure bridge on a chosen slice",
            "includes_lapse": False,
            "is_optical_lensing_amplitude": False,
            "is_qcross": False,
        },
    ]
    density_map = {
        "input": "rho_minus_proper",
        "output": "rho_minus_eff_plus_measure",
        "allowed_operation": (
            "multiply only by the metric-volume factor selected by the "
            "source equations"
        ),
        "not_allowed": [
            "use qdet_4volume_ratio as Q_cross",
            "use qdet_dust_volume_ratio as Q_cross",
            "use either Q_det factor as an optical/lensing amplitude",
            "infer the factor from raw a_minus/a_plus lensing normalization",
        ],
    }
    forbidden_lensing_amplitudes = [
        {
            "name": "raw_flrw_scale_ratio",
            "formula": "a_minus / a_plus",
            "accepted": False,
            "reason": "scale ratio alone does not fix metric-volume or optical projection",
        },
        {
            "name": "raw_det4_scale_ratio",
            "formula": "(a_minus / a_plus)^4",
            "accepted": False,
            "reason": "not a lensing amplitude; lapse and measure convention are unresolved",
        },
        {
            "name": "raw_dust3_scale_ratio",
            "formula": "(a_minus / a_plus)^3",
            "accepted": False,
            "reason": "dust volume bookkeeping is not Q_cross",
        },
    ]
    missing_for_closure = [
        "derive from Janus source equations whether Q_det uses qdet_4volume_ratio or qdet_dust_volume_ratio",
        "derive the lapse and slice convention before numerical use",
        "keep Q_det separate from Q_cross in the tensor/lensing source",
        "verify Bianchi-compatible mixed-stress transport after the convention is fixed",
    ]
    return {
        "description": "Bounded derivation artifact for Janus Q_det metric-volume mapping.",
        "definitions": definitions,
        "distinctions": distinctions,
        "density_map": density_map,
        "forbidden_lensing_amplitudes": forbidden_lensing_amplitudes,
        "accepted_raw_scale_ratio_lensing_amplitudes": [],
        "source_equation_convention_fixed": False,
        "prediction_ready": False,
        "missing_for_closure": missing_for_closure,
        "verdict": (
            "Q_det may map proper negative density into a plus-measure effective "
            "density only as a metric-volume factor. It is not Q_cross and not "
            "an optical/lensing amplitude. Prediction claims remain blocked "
            "until the source equations fix the convention."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Q_det Metric-Volume Map Derivation",
        "",
        payload["description"],
        "",
        f"Source-equation convention fixed: {payload['source_equation_convention_fixed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Definitions",
        "",
    ]
    for key, value in payload["definitions"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(
        [
            "",
            "## Distinctions",
            "",
            "| name | role | includes lapse | optical/lensing amplitude | Q_cross |",
            "|---|---|---|---|---|",
        ]
    )
    for row in payload["distinctions"]:
        lines.append(
            f"| `{row['name']}` | {row['role']} | {row['includes_lapse']} | "
            f"{row['is_optical_lensing_amplitude']} | {row['is_qcross']} |"
        )
    lines.extend(["", "## Density Map", ""])
    for key, value in payload["density_map"].items():
        if isinstance(value, list):
            lines.append(f"- `{key}`:")
            lines.extend(f"  - {item}" for item in value)
        else:
            lines.append(f"- `{key}`: {value}")
    lines.extend(["", "## Forbidden Lensing Amplitudes", ""])
    for row in payload["forbidden_lensing_amplitudes"]:
        lines.append(
            f"- `{row['name']}` `{row['formula']}` accepted={row['accepted']}: "
            f"{row['reason']}"
        )
    lines.extend(["", "## Missing For Closure", ""])
    lines.extend(f"- {item}" for item in payload["missing_for_closure"])
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.parent.mkdir(parents=True, exist_ok=True)
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
