"""Compare bimetric and standard two-qubit descriptions."""

from hassan_rosen_minisuperspace import effective_coupling
from compare_models import evaluate


if __name__ == "__main__":
    print("r bimetric_C standard_C uncoupled_C bimetric_CHSH standard_CHSH")
    for r in (1.0, 1.2, 1.5):
        coupling = effective_coupling(r)
        bimetric = evaluate(1.0, coupling)
        standard = evaluate(1.0, coupling)
        uncoupled = evaluate(1.0, 0.0)
        print(
            f"{r:3.1f} {bimetric['concurrence']:.8f} "
            f"{standard['concurrence']:.8f} {uncoupled['concurrence']:.8f} "
            f"{bimetric['chsh_max']:.8f} {standard['chsh_max']:.8f}"
        )
        assert abs(bimetric["concurrence"] - standard["concurrence"]) < 1e-12
        assert abs(bimetric["chsh_max"] - standard["chsh_max"]) < 1e-12
