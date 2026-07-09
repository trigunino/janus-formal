from __future__ import annotations

import json
from pathlib import Path


ROOT_PATH = Path("JanusFormal.lean")
BRANCH_DIR = Path("JanusFormal/Branches")
LIB_DIR = Path("JanusFormal/Lib")
LEGACY_CMB_PATH = Path("JanusFormal/Branches/LegacyCMB.lean")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_repository_layout_audit.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_repository_layout_audit.json")

OLD_UMBRELLAS = [
    Path("JanusFormal/ActiveBranches.lean"),
    Path("JanusFormal/ActiveZ2Sigma.lean"),
    Path("JanusFormal/AllImportsArchive.lean"),
]


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
    branch_heads = sorted(path.stem for path in BRANCH_DIR.glob("*.lean"))
    lib_heads = sorted(path.stem for path in LIB_DIR.glob("*.lean"))
    old_umbrellas_present = [path.as_posix() for path in OLD_UMBRELLAS if path.exists()]
    legacy_z4_scripts = _files("scripts/*z4*.py") + _files("scripts/*legacy*.py")
    legacy_z4_tests = _files("tests/test_*z4*.py") + _files("tests/test_*legacy*.py")
    daily_commands = [
        "python -m unittest tests.test_p0_eft_janus_z2_sigma_branch_head_audit_script",
        "python -m unittest tests.test_p0_eft_janus_repository_layout_audit_script",
        "lake build JanusFormal",
        "lake build JanusFormal.Branches.Z2SigmaRegular",
    ]
    return {
        "status": "janus-repository-layout-audit",
        "root_facade": ROOT_PATH.as_posix(),
        "branch_dir": BRANCH_DIR.as_posix(),
        "lib_dir": LIB_DIR.as_posix(),
        "legacy_cmb": LEGACY_CMB_PATH.as_posix(),
        "root_imports": root_imports,
        "root_facade_minimal": root_imports == ["JanusFormal.Core"],
        "branch_heads": branch_heads,
        "lib_heads": lib_heads,
        "old_umbrellas_present": old_umbrellas_present,
        "legacy_z4_script_count": len(legacy_z4_scripts),
        "legacy_z4_test_count": len(legacy_z4_tests),
        "daily_commands": daily_commands,
        "layout_clean": (
            root_imports == ["JanusFormal.Core"]
            and "Z2SigmaRegular" in branch_heads
            and "Foundation" in lib_heads
            and not old_umbrellas_present
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
        f"Branch dir: `{payload['branch_dir']}`",
        f"Lib dir: `{payload['lib_dir']}`",
        f"Layout clean: `{payload['layout_clean']}`",
        f"Old umbrellas present: `{payload['old_umbrellas_present']}`",
        "",
        "## Daily Commands",
    ]
    lines.extend(f"- `{item}`" for item in payload["daily_commands"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
