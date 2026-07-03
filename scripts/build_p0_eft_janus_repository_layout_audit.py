from __future__ import annotations

import json
from pathlib import Path


ROOT_PATH = Path("JanusFormal.lean")
ACTIVE_PATH = Path("JanusFormal/ActiveZ2Sigma.lean")
ARCHIVE_PATH = Path("JanusFormal/AllImportsArchive.lean")
LEGACY_CMB_PATH = Path("JanusFormal/LegacyCMB.lean")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_repository_layout_audit.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_repository_layout_audit.json")


def _imports(path: Path) -> list[str]:
    return [
        line.removeprefix("import ").strip()
        for line in path.read_text(encoding="utf-8").splitlines()
        if line.startswith("import ")
    ]


def _files(pattern: str) -> list[str]:
    return sorted(str(path).replace("\\", "/") for path in Path(".").glob(pattern))


def build_payload() -> dict:
    root_imports = _imports(ROOT_PATH)
    active_imports = _imports(ACTIVE_PATH)
    archive_imports = _imports(ARCHIVE_PATH)
    active_scripts = _files("scripts/*z2_sigma*.py") + _files("scripts/*active_z2_sigma*.py")
    legacy_z4_scripts = _files("scripts/*z4*.py") + _files("scripts/*legacy*.py")
    active_tests = _files("tests/test_*z2_sigma*.py") + _files("tests/test_*active_z2_sigma*.py")
    legacy_z4_tests = _files("tests/test_*z4*.py") + _files("tests/test_*legacy*.py")
    forbidden_root_archive_imports = [
        item for item in root_imports if item != "JanusFormal.ActiveZ2Sigma"
    ]
    forbidden_active_z4 = [
        item
        for item in active_imports
        if "Z4" in item and item != "JanusFormal.P0EFTJanusLegacyZ4ArchivePolicyGate"
    ]
    return {
        "status": "janus-repository-layout-audit",
        "root_facade": ROOT_PATH.as_posix(),
        "active_facade": ACTIVE_PATH.as_posix(),
        "archive_facade": ARCHIVE_PATH.as_posix(),
        "legacy_cmb_archive": LEGACY_CMB_PATH.as_posix(),
        "root_imports": root_imports,
        "root_facade_minimal": root_imports == ["JanusFormal.ActiveZ2Sigma"],
        "active_import_count": len(active_imports),
        "archive_import_count": len(archive_imports),
        "active_z2_sigma_script_count": len(active_scripts),
        "legacy_z4_script_count": len(legacy_z4_scripts),
        "active_z2_sigma_test_count": len(active_tests),
        "legacy_z4_test_count": len(legacy_z4_tests),
        "forbidden_root_archive_imports": forbidden_root_archive_imports,
        "forbidden_active_z4_imports": forbidden_active_z4,
        "daily_commands": [
            "python -m unittest tests.test_p0_eft_janus_active_z2_sigma_facade_audit_script",
            "python -m unittest tests.test_p0_eft_janus_repository_layout_audit_script",
            "lake build JanusFormal",
        ],
        "archive_commands_optional": [
            "lake build JanusFormal.AllImportsArchive",
            "python -m unittest tests.test_p0_eft_janus_z4_cmb_diagnostic_master_report_script",
        ],
        "layout_clean": (
            root_imports == ["JanusFormal.ActiveZ2Sigma"]
            and not forbidden_root_archive_imports
            and not forbidden_active_z4
            and ARCHIVE_PATH.exists()
            and LEGACY_CMB_PATH.exists()
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Repository Layout Audit",
        "",
        f"Root facade: `{payload['root_facade']}`",
        f"Active facade: `{payload['active_facade']}`",
        f"Archive facade: `{payload['archive_facade']}`",
        f"Legacy CMB archive: `{payload['legacy_cmb_archive']}`",
        f"Layout clean: `{payload['layout_clean']}`",
        "",
        "## Daily Commands",
    ]
    lines.extend(f"- `{item}`" for item in payload["daily_commands"])
    lines.extend(["", "## Archive Commands Optional"])
    lines.extend(f"- `{item}`" for item in payload["archive_commands_optional"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
