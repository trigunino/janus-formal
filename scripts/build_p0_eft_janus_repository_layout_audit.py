from __future__ import annotations

import json
from pathlib import Path


ROOT_PATH = Path("JanusFormal.lean")
BRANCH_DIR = Path("JanusFormal/Branches")
LIB_DIR = Path("JanusFormal/Lib")
HISTORICAL_BRANCH_HEADS = [
    Path("JanusFormal/Branches/CMBHistoricalDiagnostics.lean"),
    Path("JanusFormal/Branches/Z4HistoricalProgram.lean"),
    Path("JanusFormal/Branches/P0EarlyProgram.lean"),
    Path("JanusFormal/Branches/P0EFTEarlyProgram.lean"),
]
LEGACY_DIR = Path("JanusFormal/Legacy")
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
    historical_z4_scripts = _files("scripts/*z4*.py") + _files("scripts/*legacy*.py")
    historical_z4_tests = _files("tests/test_*z4*.py") + _files("tests/test_*legacy*.py")
    historical_heads_present = [path.as_posix() for path in HISTORICAL_BRANCH_HEADS if path.exists()]
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
        "historical_branch_heads": [path.as_posix() for path in HISTORICAL_BRANCH_HEADS],
        "historical_heads_present": historical_heads_present,
        "legacy_dir_present": LEGACY_DIR.exists(),
        "root_imports": root_imports,
        "root_facade_minimal": root_imports == ["JanusFormal.Core"],
        "branch_heads": branch_heads,
        "lib_heads": lib_heads,
        "old_umbrellas_present": old_umbrellas_present,
        "historical_z4_script_count": len(historical_z4_scripts),
        "historical_z4_test_count": len(historical_z4_tests),
        "daily_commands": daily_commands,
        "layout_clean": (
            root_imports == ["JanusFormal.Core"]
            and "Z2SigmaRegular" in branch_heads
            and "Foundation" in lib_heads
            and not old_umbrellas_present
            and len(historical_heads_present) == len(HISTORICAL_BRANCH_HEADS)
            and not LEGACY_DIR.exists()
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
        f"Legacy dir present: `{payload['legacy_dir_present']}`",
        "",
        "## Historical Branch Heads",
    ]
    lines.extend(f"- `{item}`" for item in payload["historical_heads_present"])
    lines.extend([
        "",
        "## Daily Commands",
    ])
    lines.extend(f"- `{item}`" for item in payload["daily_commands"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
