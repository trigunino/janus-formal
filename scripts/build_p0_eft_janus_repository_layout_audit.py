from __future__ import annotations

import json
from pathlib import Path


ROOT_PATH = Path("JanusFormal.lean")
BRANCH_DIR = Path("JanusFormal/Branches")
SHARED_DIR = Path("JanusFormal/Shared")
DIAGNOSTIC_BLOCKED_BRANCH_HEADS = [
    Path("JanusFormal/Branches/CMBPlanckDiagnosticAttempts.lean"),
    Path("JanusFormal/Branches/Z4CMBTopologyResetBlockedProgram.lean"),
    Path("JanusFormal/Branches/P0BimetricOrbifoldPrototypeProgram.lean"),
    Path("JanusFormal/Branches/P0EFTOrbifoldHolstPrototypeProgram.lean"),
]
OLD_ATTEMPTS_CATCHALL_DIR = Path("JanusFormal") / "Legacy"
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
    shared_heads = sorted(path.stem for path in SHARED_DIR.glob("*.lean"))
    old_umbrellas_present = [path.as_posix() for path in OLD_UMBRELLAS if path.exists()]
    diagnostic_z4_scripts = _files("scripts/*z4*.py")
    diagnostic_z4_tests = _files("tests/test_*z4*.py")
    diagnostic_blocked_heads_present = [
        path.as_posix() for path in DIAGNOSTIC_BLOCKED_BRANCH_HEADS if path.exists()
    ]
    daily_commands = [
        "python -m unittest tests.test_p0_eft_janus_z2_sigma_branch_head_audit_script",
        "python -m unittest tests.test_p0_eft_janus_repository_layout_audit_script",
        "lake build JanusFormal",
        "lake build JanusFormal.Branches.Z2SigmaRegularThroat",
    ]
    return {
        "status": "janus-repository-layout-audit",
        "root_facade": ROOT_PATH.as_posix(),
        "branch_dir": BRANCH_DIR.as_posix(),
        "shared_dir": SHARED_DIR.as_posix(),
        "diagnostic_blocked_branch_heads": [
            path.as_posix() for path in DIAGNOSTIC_BLOCKED_BRANCH_HEADS
        ],
        "diagnostic_blocked_heads_present": diagnostic_blocked_heads_present,
        "old_attempts_catchall_dir_present": OLD_ATTEMPTS_CATCHALL_DIR.exists(),
        "root_imports": root_imports,
        "root_facade_minimal": root_imports == ["JanusFormal.Core"],
        "branch_heads": branch_heads,
        "shared_heads": shared_heads,
        "old_umbrellas_present": old_umbrellas_present,
        "diagnostic_z4_script_count": len(diagnostic_z4_scripts),
        "diagnostic_z4_test_count": len(diagnostic_z4_tests),
        "daily_commands": daily_commands,
        "layout_clean": (
            root_imports == ["JanusFormal.Core"]
            and "Z2SigmaRegularThroat" in branch_heads
            and "Foundation" in shared_heads
            and not old_umbrellas_present
            and len(diagnostic_blocked_heads_present) == len(DIAGNOSTIC_BLOCKED_BRANCH_HEADS)
            and not OLD_ATTEMPTS_CATCHALL_DIR.exists()
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
        f"Shared dir: `{payload['shared_dir']}`",
        f"Layout clean: `{payload['layout_clean']}`",
        f"Old umbrellas present: `{payload['old_umbrellas_present']}`",
        f"Old-attempts catchall dir present: `{payload['old_attempts_catchall_dir_present']}`",
        "",
        "## Diagnostic And Blocked Branch Heads",
    ]
    lines.extend(f"- `{item}`" for item in payload["diagnostic_blocked_heads_present"])
    lines.extend([
        "",
        "## Daily Commands",
    ])
    lines.extend(f"- `{item}`" for item in payload["daily_commands"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
