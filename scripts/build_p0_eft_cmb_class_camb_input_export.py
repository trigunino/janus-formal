from __future__ import annotations

from pathlib import Path
import csv
import json
import math

try:
    from scripts.build_p0_eft_cmb_visibility_physical import build_payload as visibility_payload, visibility_physical
    from scripts.build_p0_eft_cmb_weyl_transfer_integration import mu_janus_holst, sigma_janus_holst
    from scripts.build_p0_eft_janus_holst_distance_ruler_map import (
        e2_janus_holst,
        master_branch_background,
    )
    from scripts.build_p0_eft_cmb_full_hierarchy_pre_likelihood import primordial_power
except ModuleNotFoundError:
    from build_p0_eft_cmb_visibility_physical import build_payload as visibility_payload, visibility_physical
    from build_p0_eft_cmb_weyl_transfer_integration import mu_janus_holst, sigma_janus_holst
    from build_p0_eft_janus_holst_distance_ruler_map import e2_janus_holst, master_branch_background
    from build_p0_eft_cmb_full_hierarchy_pre_likelihood import primordial_power


OUT_DIR = Path("outputs/cmb_bridge")
REPORT_PATH = Path("outputs/reports/p0_eft_cmb_class_camb_input_export.md")
JSON_PATH = Path("outputs/reports/p0_eft_cmb_class_camb_input_export.json")


def write_csv(path: Path, rows: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def build_payload() -> dict:
    constants, radion = master_branch_background()
    screened = {**constants, "spin_coeff": 0.0}
    visibility = visibility_payload()
    a_rows = []
    for i in range(301):
        loga = -8.0 + i * (8.0 / 300.0)
        a = math.exp(loga)
        e2 = e2_janus_holst(a, screened, radion)
        a_rows.append({"a": a, "z": 1.0 / a - 1.0, "E": math.sqrt(e2), "E2": e2})
    k_values = [10 ** (-4 + i * (4.0 / 80.0)) for i in range(81)]
    mg_rows = []
    for k in k_values:
        for a in [0.001, 0.003, 0.01, 0.03, 0.1, 0.3, 0.667, 1.0]:
            mg_rows.append(
                {
                    "k": k,
                    "a": a,
                    "mu_JH": mu_janus_holst(k, a, screened, radion),
                    "Sigma_JH": sigma_janus_holst(k, a, screened, radion),
                }
            )
    z_rows = []
    for i in range(701):
        z = 700.0 + (1400.0 - 700.0) * i / 700.0
        z_rows.append(
            {
                "z": z,
                "visibility": visibility_physical(z, visibility["z_star"], visibility["sigma_z"]),
                "z_star": visibility["z_star"],
                "sigma_z": visibility["sigma_z"],
            }
        )
    pk_rows = [{"k": k, "P_R": primordial_power(k)} for k in k_values]
    files = {
        "background": OUT_DIR / "janus_holst_background.csv",
        "modified_gravity": OUT_DIR / "janus_holst_mu_sigma.csv",
        "visibility": OUT_DIR / "janus_holst_visibility.csv",
        "primordial": OUT_DIR / "janus_holst_primordial.csv",
    }
    write_csv(files["background"], a_rows)
    write_csv(files["modified_gravity"], mg_rows)
    write_csv(files["visibility"], z_rows)
    write_csv(files["primordial"], pk_rows)
    manifest = {
        "description": "CLASS/CAMB input tables for Janus-Holst CMB bridge.",
        "status": "class-camb-input-tables-exported",
        "files": {key: str(value) for key, value in files.items()},
        "adapter_written": False,
        "external_solver_run": False,
        "direct_cmb_likelihood_ready": False,
    }
    (OUT_DIR / "manifest.json").write_text(json.dumps(manifest, indent=2), encoding="utf-8")
    return {
        **manifest,
        "row_counts": {
            "background": len(a_rows),
            "modified_gravity": len(mg_rows),
            "visibility": len(z_rows),
            "primordial": len(pk_rows),
        },
        "next_required": "write a CLASS/CAMB adapter that reads outputs/cmb_bridge/manifest.json.",
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT CMB CLASS/CAMB Input Export",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Adapter written: {payload['adapter_written']}",
        f"External solver run: {payload['external_solver_run']}",
        f"Direct CMB likelihood ready: {payload['direct_cmb_likelihood_ready']}",
        "",
        "## Files",
        "",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["files"].items())
    lines.extend(["", "## Row Counts", ""])
    lines.extend(f"- `{key}`: {value}" for key, value in payload["row_counts"].items())
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
    print(f"Wrote {OUT_DIR / 'manifest.json'}")


if __name__ == "__main__":
    main()
