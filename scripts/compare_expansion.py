from __future__ import annotations

from pathlib import Path

import numpy as np

from janus_lab import JanusExpansion, distance_modulus, e_cpl, e_lcdm


def main() -> None:
    out_dir = Path("outputs/figures")
    out_dir.mkdir(parents=True, exist_ok=True)

    z = np.linspace(0.001, 2.5, 300)
    janus = JanusExpansion(u0=4.0)

    models = {
        "Lambda-CDM": lambda x: e_lcdm(x, omega_m=0.315),
        "CPL example": lambda x: e_cpl(x, omega_m=0.315, w0=-0.85, wa=-0.7),
        "Janus exact example": janus.e,
    }

    columns = [z]
    header = ["z"]
    for label, e_func in models.items():
        safe_label = label.lower().replace(" ", "_").replace("-", "_")
        columns.append(e_func(z))
        columns.append(distance_modulus(z, e_func, h0=70.0, samples=1024))
        header.extend([f"{safe_label}_e", f"{safe_label}_mu"])

    csv_output = out_dir / "expansion_comparison.csv"
    np.savetxt(
        csv_output,
        np.column_stack(columns),
        delimiter=",",
        header=",".join(header),
        comments="",
    )
    print(f"Wrote {csv_output}")

    try:
        import matplotlib.pyplot as plt
    except ModuleNotFoundError:
        print("matplotlib is not installed; skipped PNG plot.")
        return

    fig, axes = plt.subplots(1, 2, figsize=(11, 4.5), constrained_layout=True)
    for label, e_func in models.items():
        axes[0].plot(z, e_func(z), label=label)
        axes[1].plot(z, distance_modulus(z, e_func, h0=70.0, samples=1024), label=label)

    axes[0].set_title("Expansion")
    axes[0].set_xlabel("redshift z")
    axes[0].set_ylabel("H(z) / H0")
    axes[0].grid(alpha=0.25)
    axes[0].legend()

    axes[1].set_title("Distance modulus")
    axes[1].set_xlabel("redshift z")
    axes[1].set_ylabel("mu(z)")
    axes[1].grid(alpha=0.25)

    png_output = out_dir / "expansion_comparison.png"
    fig.savefig(png_output, dpi=160)
    print(f"Wrote {png_output}")


if __name__ == "__main__":
    main()
