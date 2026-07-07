from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from janus_lab.z2_sigma_background_inputs import (
    build_active_z2sigma_background_scalar_payload,
)


H0_PATH = Path("outputs/active_z2_sigma/background_H0_normalization_inputs.json")
RADIUS_PATH = Path(
    "outputs/active_z2_sigma/background_curvature_radius_normalization_inputs.json"
)
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_effective_dimensional_anchor_input.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_effective_dimensional_anchor_input.json"
)
FORBIDDEN_PROVENANCE_TOKENS = ("planck", "lcdm", "z4", "fit", "bao_scan", "demo")


def _clean_effective_provenance(provenance: str) -> str:
    text = str(provenance).strip()
    if not text:
        raise ValueError("effective dimensional anchor provenance must be nonempty")
    lowered = text.lower()
    if any(token in lowered for token in FORBIDDEN_PROVENANCE_TOKENS):
        raise ValueError(f"Forbidden effective dimensional anchor provenance: {text}")
    return text


def _base_payload() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
    }


def _scalar_payload(field: str, value: float, provenance_key: str, provenance: str) -> dict:
    payload = _base_payload()
    payload["scalars"] = {field: value}
    payload["scalar_provenance"] = {
        provenance_key: f"effective_initial_state:{provenance}"
    }
    return build_active_z2sigma_background_scalar_payload(payload, field)


def build_payload(
    *,
    h0_km_s_mpc: float | None = None,
    r_curv_mpc: float | None = None,
    provenance: str,
) -> dict:
    if h0_km_s_mpc is None and r_curv_mpc is None:
        raise ValueError("At least one dimensional anchor must be provided")
    provenance = _clean_effective_provenance(provenance)
    anchors: dict[str, dict] = {}
    if h0_km_s_mpc is not None:
        anchors["H0_Z2Sigma"] = _scalar_payload(
            "H0_Z2Sigma_km_s_Mpc",
            h0_km_s_mpc,
            "H0_Z2Sigma",
            provenance,
        )
    if r_curv_mpc is not None:
        anchors["R_curv_Z2Sigma"] = _scalar_payload(
            "R_curv_Z2Sigma_Mpc",
            r_curv_mpc,
            "R_curv_Z2Sigma",
            provenance,
        )
    return {
        "status": "janus-z2-sigma-effective-dimensional-anchor-input",
        "active_core": "Z2_tunnel_Sigma",
        "branch": "effective_initial_state",
        "no_fit_branch_closed": False,
        "full_no_fit_prediction_ready": False,
        "anchors": anchors,
        "gate_passed": True,
    }


def write_outputs(payload: dict) -> dict:
    written: dict[str, str] = {}
    if "H0_Z2Sigma" in payload["anchors"]:
        H0_PATH.parent.mkdir(parents=True, exist_ok=True)
        H0_PATH.write_text(
            json.dumps(payload["anchors"]["H0_Z2Sigma"], indent=2),
            encoding="utf-8",
        )
        written["H0_Z2Sigma"] = str(H0_PATH)
    if "R_curv_Z2Sigma" in payload["anchors"]:
        RADIUS_PATH.parent.mkdir(parents=True, exist_ok=True)
        RADIUS_PATH.write_text(
            json.dumps(payload["anchors"]["R_curv_Z2Sigma"], indent=2),
            encoding="utf-8",
        )
        written["R_curv_Z2Sigma"] = str(RADIUS_PATH)
    payload = dict(payload)
    payload["written_manifests"] = written
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2/Sigma Effective Dimensional Anchor Input",
                "",
                f"Branch: `{payload['branch']}`",
                f"No-fit branch closed: `{payload['no_fit_branch_closed']}`",
                f"Full no-fit prediction ready: `{payload['full_no_fit_prediction_ready']}`",
                f"Written manifests: `{written}`",
            ]
        ),
        encoding="utf-8",
    )
    return payload


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Write explicit effective dimensional anchor inputs for Z2/Sigma."
    )
    parser.add_argument("--h0-km-s-mpc", type=float)
    parser.add_argument("--r-curv-mpc", type=float)
    parser.add_argument("--provenance", required=True)
    args = parser.parse_args()
    print(
        json.dumps(
            write_outputs(
                build_payload(
                    h0_km_s_mpc=args.h0_km_s_mpc,
                    r_curv_mpc=args.r_curv_mpc,
                    provenance=args.provenance,
                )
            ),
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
