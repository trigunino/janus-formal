from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_tracefree_h_isotropy_no_go_gate.md")
JSON_PATH = Path("outputs/reports/p0_tracefree_h_isotropy_no_go_gate.json")


def build_payload() -> dict:
    dimension = 4
    symmetric_rank = dimension * (dimension + 1) // 2
    tracefree_rank = symmetric_rank - 1
    rows = [
        {
            "source": "density_scalar",
            "form": "rho * H or rho * identity",
            "tracefree_projection": "zero",
            "selects_q_tf": False,
        },
        {
            "source": "pressure_scalar",
            "form": "p * h_mu_nu",
            "tracefree_projection": "zero",
            "selects_q_tf": False,
        },
        {
            "source": "determinant_or_B4vol",
            "form": "single trace scalar",
            "tracefree_projection": "zero",
            "selects_q_tf": False,
        },
        {
            "source": "exact_FLRW_branch",
            "form": "homogeneous and isotropic metric sector",
            "tracefree_projection": "forces Q_TF=0 only inside that branch",
            "selects_q_tf": False,
        },
    ]
    return {
        "description": "No-go gate for selecting trace-free H/Q_TF from isotropic Janus scalar data.",
        "status": "tracefree-h-isotropy-no-go-open",
        "dimension": dimension,
        "rank_counts": {
            "symmetric_H_components": symmetric_rank,
            "tracefree_H_components": tracefree_rank,
            "scalar_isotropic_channels": 1,
        },
        "rows": rows,
        "isotropic_sources_have_zero_tf_projection": True,
        "flrw_sets_q_tf_zero_conditionally": True,
        "flrw_selects_perturbative_tensor_closure": False,
        "source_tracefree_h_selected": False,
        "accepted_as_prediction_input": False,
        "prediction_ready": False,
        "verdict": (
            "Density, pressure, determinant and exact FLRW data are scalar or isotropic. "
            "Their trace-free projection cannot select the 9-component Q_TF/H_TF sector. "
            "FLRW may consistently impose Q_TF=0 only as a conditional background branch, "
            "not as the perturbative or lensing tensor closure needed for prediction."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Trace-Free H Isotropy No-Go Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Dimension: {payload['dimension']}",
        f"Isotropic sources have zero TF projection: {payload['isotropic_sources_have_zero_tf_projection']}",
        f"FLRW sets Q_TF zero conditionally: {payload['flrw_sets_q_tf_zero_conditionally']}",
        f"FLRW selects perturbative tensor closure: {payload['flrw_selects_perturbative_tensor_closure']}",
        f"Source trace-free H selected: {payload['source_tracefree_h_selected']}",
        f"Accepted as prediction input: {payload['accepted_as_prediction_input']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Rank Counts",
        "",
    ]
    for key, value in payload["rank_counts"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Rejected Isotropic Sources", "", "| source | form | TF projection | selects Q_TF |", "|---|---|---|---:|"])
    for row in payload["rows"]:
        lines.append(
            f"| {row['source']} | {row['form']} | {row['tracefree_projection']} | {row['selects_q_tf']} |"
        )
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
