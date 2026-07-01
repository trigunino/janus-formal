from __future__ import annotations

from pathlib import Path
import importlib.util
import json

try:
    from scripts.build_p0_eft_cmb_class_camb_input_export import build_payload as export_payload
except ModuleNotFoundError:
    from build_p0_eft_cmb_class_camb_input_export import build_payload as export_payload


OUT_DIR = Path("outputs/cmb_bridge")
REPORT_PATH = Path("outputs/reports/p0_eft_cmb_class_camb_adapter.md")
JSON_PATH = Path("outputs/reports/p0_eft_cmb_class_camb_adapter.json")


def backend_available(name: str) -> bool:
    return importlib.util.find_spec(name) is not None


def write_class_ini(files: dict[str, str]) -> Path:
    path = OUT_DIR / "class_janus_holst_adapter.ini"
    text = "\n".join(
        [
            "# Janus-Holst CLASS fork adapter stub.",
            "# A stock CLASS build will not understand these custom table keys.",
            "output = tCl,pCl,lCl,mPk",
            "l_max_scalars = 2500",
            "lensing = yes",
            f"janus_background_table = {files['background']}",
            f"janus_mu_sigma_table = {files['modified_gravity']}",
            f"janus_visibility_table = {files['visibility']}",
            f"janus_primordial_table = {files['primordial']}",
            "janus_spin_background_projection = 0",
            "janus_delta_neff_relation = eta_abs_times_omega_m0",
            "",
        ]
    )
    path.write_text(text, encoding="utf-8")
    return path


def write_camb_json(files: dict[str, str]) -> Path:
    path = OUT_DIR / "camb_janus_holst_adapter.json"
    payload = {
        "note": "Adapter payload for a CAMB fork or wrapper with Janus custom sources.",
        "outputs": ["TT", "TE", "EE", "lens_potential", "matter_transfer"],
        "lmax": 2500,
        "lensing": True,
        "janus_tables": files,
        "spin_background_projection": 0.0,
        "delta_neff_relation": "Delta_Neff_Holst = abs(eta_H) * Omega_m0",
    }
    path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    return path


def write_runner(class_ini: Path, camb_json: Path) -> Path:
    path = OUT_DIR / "run_external_boltzmann_adapter.ps1"
    text = "\n".join(
        [
            "# Manual runner for a local CLASS/CAMB fork.",
            "# Edit paths below to point to your compiled external solver.",
            "$CLASS_EXE = 'C:/path/to/class.exe'",
            "$CAMB_WRAPPER = 'C:/path/to/camb_wrapper.py'",
            f"$CLASS_INI = '{class_ini.as_posix()}'",
            f"$CAMB_JSON = '{camb_json.as_posix()}'",
            "Write-Host 'CLASS config:' $CLASS_INI",
            "Write-Host 'CAMB payload:' $CAMB_JSON",
            "# & $CLASS_EXE $CLASS_INI",
            "# python $CAMB_WRAPPER $CAMB_JSON",
            "",
        ]
    )
    path.write_text(text, encoding="utf-8")
    return path


def build_payload() -> dict:
    export = export_payload()
    files = export["files"]
    class_ini = write_class_ini(files)
    camb_json = write_camb_json(files)
    runner = write_runner(class_ini, camb_json)
    camb_installed = backend_available("camb")
    classy_installed = backend_available("classy")
    return {
        "description": "CLASS/CAMB adapter files for Janus-Holst CMB bridge.",
        "status": "class-camb-adapter-written-external-run-open",
        "input_manifest": str(OUT_DIR / "manifest.json"),
        "class_ini": str(class_ini),
        "camb_json": str(camb_json),
        "runner_script": str(runner),
        "python_camb_available": camb_installed,
        "python_classy_available": classy_installed,
        "adapter_written": True,
        "external_solver_run": False,
        "external_validation_passed": False,
        "direct_cmb_likelihood_ready": False,
        "next_required": "install or point to a CLASS/CAMB fork that supports the Janus custom table keys, then run the generated adapter.",
    }


def render_markdown(payload: dict) -> str:
    return "\n".join(
        [
            "# P0 EFT CMB CLASS/CAMB Adapter",
            "",
            payload["description"],
            "",
            f"Status: {payload['status']}",
            f"Python camb available: {payload['python_camb_available']}",
            f"Python classy available: {payload['python_classy_available']}",
            f"Adapter written: {payload['adapter_written']}",
            f"External solver run: {payload['external_solver_run']}",
            f"Direct CMB likelihood ready: {payload['direct_cmb_likelihood_ready']}",
            "",
            "## Files",
            "",
            f"- CLASS ini: `{payload['class_ini']}`",
            f"- CAMB json: `{payload['camb_json']}`",
            f"- runner: `{payload['runner_script']}`",
            "",
            "## Next",
            "",
            payload["next_required"],
            "",
        ]
    )


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
