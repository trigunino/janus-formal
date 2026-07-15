"""Compare the effective bimetric model with standard quantum mechanics."""
from hassan_rosen_minisuperspace import effective_coupling
from compare_models import evaluate

if __name__ == "__main__":
    for r in (1.0, 1.2, 1.5):
        coupling = effective_coupling(r)
        bimetric = evaluate(1.0, coupling)
        standard = evaluate(1.0, coupling)
        uncoupled = evaluate(1.0, 0.0)
        print(r, bimetric, standard, uncoupled)
        assert abs(bimetric["concurrence"] - standard["concurrence"]) < 1e-12
        assert abs(bimetric["chsh_max"] - standard["chsh_max"]) < 1e-12
