from __future__ import annotations

import json
from pathlib import Path


ROOT_PATH = Path("JanusFormal.lean")
BRANCH_HEAD = Path("JanusFormal/Branches/Z2SigmaRegularThroat.lean")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_branch_head_audit.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_branch_head_audit.json")

SUBHEADS = [
    "Foundation",
    "Topology",
    "GeometryEmbedding",
    "BoundaryDynamics",
    "MatterPlasmaSpinor",
    "TransportForce",
    "GlobalBimetricAlpha",
    "Observables",
]

OLD_FACADES = [
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


def build_payload() -> dict:
    root_imports = _imports(ROOT_PATH)
    branch_imports = _imports(BRANCH_HEAD)
    expected_branch_imports = [
        f"JanusFormal.Branches.Z2SigmaRegularThroat.{name}" for name in SUBHEADS
    ]
    subhead_paths = [
        Path(f"JanusFormal/Branches/Z2SigmaRegularThroat/{name}.lean") for name in SUBHEADS
    ]
    subhead_import_counts = {
        path.stem: len(_imports(path)) for path in subhead_paths if path.exists()
    }
    old_facades_present = [path.as_posix() for path in OLD_FACADES if path.exists()]
    return {
        "status": "janus-z2-sigma-branch-head-audit",
        "root": ROOT_PATH.as_posix(),
        "branch_head": BRANCH_HEAD.as_posix(),
        "root_imports": root_imports,
        "root_facade_minimal": root_imports == ["JanusFormal.Core"],
        "branch_imports": branch_imports,
        "expected_branch_imports": expected_branch_imports,
        "branch_head_split": branch_imports == expected_branch_imports,
        "subhead_import_counts": subhead_import_counts,
        "old_facades_present": old_facades_present,
        "branch_layout_clean": (
            root_imports == ["JanusFormal.Core"]
            and branch_imports == expected_branch_imports
            and len(subhead_import_counts) == len(SUBHEADS)
            and not old_facades_present
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Branch Head Audit",
        "",
        f"Root facade minimal: `{payload['root_facade_minimal']}`",
        f"Branch head: `{payload['branch_head']}`",
        f"Branch head split: `{payload['branch_head_split']}`",
        f"Old facades present: `{payload['old_facades_present']}`",
        "",
        "## Subhead Import Counts",
    ]
    lines.extend(
        f"- `{name}`: `{count}`"
        for name, count in payload["subhead_import_counts"].items()
    )
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
