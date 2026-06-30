from __future__ import annotations

import shutil
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
LEAN_FILE = ROOT / "formal" / "lean" / "JanusBasic.lean"


def run(command: list[str]) -> int:
    print("+ " + " ".join(command))
    return subprocess.call(command, cwd=ROOT)


def main() -> None:
    status = run([sys.executable, "scripts/check_symbolic_formulas.py"])
    if status != 0:
        raise SystemExit(status)

    if shutil.which("lean"):
        status = run(["lean", str(LEAN_FILE)])
        if status != 0:
            raise SystemExit(status)
    else:
        print("SKIP: Lean not installed; see formal/lean/README.md")


if __name__ == "__main__":
    main()

