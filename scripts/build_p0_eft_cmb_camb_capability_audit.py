from __future__ import annotations

from pathlib import Path
import csv
import importlib.util
import inspect
import json

REPORT_PATH = Path("outputs/reports/p0_eft_cmb_camb_capability_audit.md")
JSON_PATH = Path("outputs/reports/p0_eft_cmb_camb_capability_audit.json")
MANIFEST_PATH = Path("outputs/cmb_bridge/manifest.json")


def module_available(name: str) -> bool:
    return importlib.util.find_spec(name) is not None


def table_columns(path: str) -> list[str]:
    with Path(path).open(newline="", encoding="utf-8") as handle:
        return next(csv.reader(handle))


def build_payload() -> dict:
    camb_available = module_available("camb")
    symbolic_available = module_available("camb.symbolic")
    custom_source_signature = None
    custom_source_doc_mentions_sympy = False
    if camb_available:
        import camb

        method = camb.CAMBparams.set_custom_scalar_sources
        custom_source_signature = str(inspect.signature(method))
        custom_source_doc_mentions_sympy = "sympy" in (inspect.getdoc(method) or "").lower()

    manifest = json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))
    files = manifest["files"]
    mg_columns = table_columns(files["modified_gravity"])
    background_columns = table_columns(files["background"])
    janus_tables_are_tabulated = "mu_JH" in mg_columns and "Sigma_JH" in mg_columns

    stock_camb_accepts_tabulated_mg = False
    requires_fork_or_wrapper = janus_tables_are_tabulated and not stock_camb_accepts_tabulated_mg
    payload = {
        "description": "Capability audit for using installed CAMB with Janus-Holst CMB bridge tables.",
        "status": "camb-capability-audited",
        "python_camb_available": camb_available,
        "camb_symbolic_available": symbolic_available,
        "custom_scalar_sources_available": custom_source_signature is not None,
        "custom_scalar_sources_signature": custom_source_signature,
        "custom_scalar_sources_are_symbolic": custom_source_doc_mentions_sympy,
        "janus_modified_gravity_columns": mg_columns,
        "janus_background_columns": background_columns,
        "janus_tables_are_tabulated": janus_tables_are_tabulated,
        "stock_camb_accepts_tabulated_mu_sigma": stock_camb_accepts_tabulated_mg,
        "requires_camb_fork_or_wrapper": requires_fork_or_wrapper,
        "direct_cmb_likelihood_ready": False,
        "next_required": "Implement a CAMB wrapper/fork layer mapping tabulated Janus mu/Sigma(k,a) into CAMB source evolution.",
    }
    return payload


def render_markdown(payload: dict) -> str:
    return "\n".join(
        [
            "# P0 EFT CMB CAMB Capability Audit",
            "",
            payload["description"],
            "",
            f"Status: {payload['status']}",
            f"Python CAMB available: {payload['python_camb_available']}",
            f"CAMB symbolic available: {payload['camb_symbolic_available']}",
            f"Custom scalar sources available: {payload['custom_scalar_sources_available']}",
            f"Custom scalar sources are symbolic: {payload['custom_scalar_sources_are_symbolic']}",
            f"Janus tables are tabulated: {payload['janus_tables_are_tabulated']}",
            f"Stock CAMB accepts tabulated mu/Sigma: {payload['stock_camb_accepts_tabulated_mu_sigma']}",
            f"Requires CAMB fork/wrapper: {payload['requires_camb_fork_or_wrapper']}",
            f"Direct CMB likelihood ready: {payload['direct_cmb_likelihood_ready']}",
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
