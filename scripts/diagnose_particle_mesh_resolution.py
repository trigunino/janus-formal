from __future__ import annotations

from pathlib import Path

import numpy as np

from janus_lab.particle_mesh import particle_mesh_accelerations
from janus_lab.signed_sector import BodyState, Sector


REPORT_PATH = Path("outputs/reports/particle_mesh_resolution.md")
CSV_PATH = Path("outputs/reports/particle_mesh_resolution.csv")


def pair(second_sector: Sector) -> list[BodyState]:
    return [
        BodyState(np.asarray([0.35, 0.5]), np.zeros(2), 1.0, Sector.POSITIVE),
        BodyState(np.asarray([0.65, 0.5]), np.zeros(2), 1.0, second_sector),
    ]


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    rows = []
    for grid_n in (16, 32, 64):
        for case_name, second_sector in (
            ("positive_positive", Sector.POSITIVE),
            ("positive_negative", Sector.NEGATIVE),
        ):
            bodies = pair(second_sector)
            accelerations = particle_mesh_accelerations(
                bodies,
                grid_shape=(grid_n, grid_n),
                box_size=1.0,
            )
            rows.append(
                {
                    "grid_n": grid_n,
                    "case": case_name,
                    "ax_body_0": float(accelerations[0][0]),
                    "ax_body_1": float(accelerations[1][0]),
                }
            )

    with CSV_PATH.open("w", encoding="utf-8") as handle:
        handle.write("grid_n,case,ax_body_0,ax_body_1\n")
        for row in rows:
            handle.write(
                f"{row['grid_n']},{row['case']},"
                f"{row['ax_body_0']:.10g},{row['ax_body_1']:.10g}\n"
            )

    lines = [
        "# Particle-Mesh Resolution Diagnostic",
        "",
        "Initial x-accelerations for the same two-particle setup at several grid resolutions.",
        "",
        "| grid n | case | ax body 0 | ax body 1 | sign check |",
        "|---:|---|---:|---:|---|",
    ]
    for row in rows:
        if row["case"] == "positive_positive":
            sign_check = "attraction" if row["ax_body_0"] > 0.0 and row["ax_body_1"] < 0.0 else "fail"
        else:
            sign_check = "repulsion" if row["ax_body_0"] < 0.0 and row["ax_body_1"] > 0.0 else "fail"
        lines.append(
            f"| {row['grid_n']} | {row['case']} | {row['ax_body_0']:.6g} | "
            f"{row['ax_body_1']:.6g} | {sign_check} |"
        )
    lines.extend(
        [
            "",
            f"CSV: `{CSV_PATH}`",
            "",
            "Boundary: this checks numerical sign stability only. It is not a physical calibration or observational fit.",
            "",
        ]
    )
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {CSV_PATH}")


if __name__ == "__main__":
    main()
