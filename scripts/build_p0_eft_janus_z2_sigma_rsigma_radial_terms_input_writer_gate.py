from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_rsigma_radial_terms import (
    load_active_z2sigma_rsigma_radial_term_manifest,
    merge_active_z2sigma_rsigma_radial_terms,
    write_active_z2sigma_rsigma_radial_terms_input_manifest,
)


TERM_PATHS = {
    "E_CartanGHY": Path("outputs/active_z2_sigma/rsigma_E_CartanGHY.json"),
    "E_HolstNiehYan": Path("outputs/active_z2_sigma/rsigma_E_HolstNiehYan.json"),
    "E_matterFlux": Path("outputs/active_z2_sigma/rsigma_E_matterFlux.json"),
    "E_counterterm": Path("outputs/active_z2_sigma/rsigma_E_counterterm.json"),
}
CERTIFICATE_PAYLOAD_PATH = Path("outputs/active_z2_sigma/rsigma_certificate_payload.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/rsigma_radial_terms_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_rsigma_radial_terms_input_writer_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_rsigma_radial_terms_input_writer_gate.json")


def build_payload(
    *,
    term_paths: dict[str, Path] | None = None,
    certificate_payload_path: Path = CERTIFICATE_PAYLOAD_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    paths = term_paths if term_paths is not None else TERM_PATHS
    input_exists = {name: path.exists() for name, path in paths.items()}
    input_exists["certificate_payload"] = certificate_payload_path.exists()
    output_written = False
    validation_error = None
    if all(input_exists.values()):
        try:
            terms = {
                name: load_active_z2sigma_rsigma_radial_term_manifest(
                    path,
                    expected_term_name=name,
                )
                for name, path in paths.items()
            }
            certificate_payload = json.loads(certificate_payload_path.read_text(encoding="utf-8"))
            merged = merge_active_z2sigma_rsigma_radial_terms(
                cartan_ghy_payload=terms["E_CartanGHY"],
                holst_nieh_yan_payload=terms["E_HolstNiehYan"],
                matter_flux_payload=terms["E_matterFlux"],
                counterterm_payload=terms["E_counterterm"],
                certificate_payload=certificate_payload,
            )
            write_active_z2sigma_rsigma_radial_terms_input_manifest(output_path, merged)
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    missing = [name for name, exists in input_exists.items() if not exists]
    return {
        "status": "janus-z2-sigma-rsigma-radial-terms-input-writer-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifests": {name: str(path) for name, path in paths.items()},
        "certificate_payload_manifest": str(certificate_payload_path),
        "output_manifest": str(output_path),
        "input_exists": input_exists,
        "missing_inputs": missing,
        "radial_terms_input_written": output_written,
        "gate_passed": output_written,
        "primary_blocker": "none" if output_written else "R_Sigma_radial_terms_inputs",
        "validation_error": validation_error,
        "next_required": []
        if output_written
        else [
            "derive_E_CartanGHY_radial_term_manifest",
            "derive_E_HolstNiehYan_radial_term_manifest",
            "derive_E_matterFlux_radial_term_manifest",
            "derive_E_counterterm_radial_term_manifest",
            "supply_matching_rsigma_certificate_payload_manifest",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma R_Sigma Radial Terms Input Writer Gate",
        "",
        f"Missing inputs: `{payload['missing_inputs']}`",
        f"Output written: `{payload['radial_terms_input_written']}`",
        f"Gate passed: `{payload['gate_passed']}`",
    ]
    if payload["validation_error"]:
        lines.extend(["", "## Validation Error", payload["validation_error"]])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
