from __future__ import annotations

from pathlib import Path
import csv
import json

try:
    from scripts.build_p0_eft_cmb_class_camb_adapter import build_payload as adapter_payload
    from scripts.build_p0_eft_cmb_full_hierarchy_pre_likelihood import build_payload as pre_likelihood_payload
except ModuleNotFoundError:
    from build_p0_eft_cmb_class_camb_adapter import build_payload as adapter_payload
    from build_p0_eft_cmb_full_hierarchy_pre_likelihood import build_payload as pre_likelihood_payload


REPORT_PATH = Path("outputs/reports/p0_eft_cmb_local_boltzmann_adapter_runner.md")
JSON_PATH = Path("outputs/reports/p0_eft_cmb_local_boltzmann_adapter_runner.json")
CSV_PATH = Path("outputs/cmb_bridge/local_adapter_spectra_proxy.csv")


def read_csv_rows(path: str) -> list[dict]:
    with Path(path).open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle))


def build_payload() -> dict:
    adapter = adapter_payload()
    pre = pre_likelihood_payload()
    manifest = json.loads(Path(adapter["input_manifest"]).read_text(encoding="utf-8"))
    tables = {key: read_csv_rows(path) for key, path in manifest["files"].items()}
    spectra = pre["spectra_proxy"]
    CSV_PATH.parent.mkdir(parents=True, exist_ok=True)
    with CSV_PATH.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(spectra[0].keys()))
        writer.writeheader()
        writer.writerows(spectra)
    row_counts = {key: len(value) for key, value in tables.items()}
    required_ok = all(count > 0 for count in row_counts.values()) and len(spectra) > 0
    return {
        "description": "Local fallback runner for the Janus-Holst CMB adapter contract.",
        "status": "local-boltzmann-adapter-runner-produced-proxy-output",
        "input_manifest": adapter["input_manifest"],
        "row_counts": row_counts,
        "local_proxy_output": str(CSV_PATH),
        "tables_valid": required_ok,
        "external_solver_run": False,
        "local_proxy_run": True,
        "external_validation_passed": False,
        "direct_cmb_likelihood_ready": False,
        "next_required": "use local_adapter_spectra_proxy.csv as a smoke-test target when connecting a real CLASS/CAMB fork.",
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT CMB Local Boltzmann Adapter Runner",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Tables valid: {payload['tables_valid']}",
        f"Local proxy run: {payload['local_proxy_run']}",
        f"External solver run: {payload['external_solver_run']}",
        f"Direct CMB likelihood ready: {payload['direct_cmb_likelihood_ready']}",
        "",
        "## Row Counts",
        "",
    ]
    lines.extend(f"- `{key}`: {value}" for key, value in payload["row_counts"].items())
    lines.extend(["", "## Output", "", f"- `{payload['local_proxy_output']}`", "", "## Next", "", payload["next_required"], ""])
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
    print(f"Wrote {CSV_PATH}")


if __name__ == "__main__":
    main()
