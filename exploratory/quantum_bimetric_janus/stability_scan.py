"""Sanity scan for the action-inspired toy coupling."""

from action_ansatz import induced_coupling_from_action
from compare_models import evaluate


if __name__ == "__main__":
    worst_norm = 0.0
    largest_chsh = 0.0
    for beta in (0.01, 0.1, 0.5, 1.0):
        for c in (0.5, 0.8, 1.0, 1.2, 1.5):
            result = evaluate(
                omega_minus=1.0,
                coupling=induced_coupling_from_action(c, beta),
            )
            worst_norm = max(worst_norm, result["norm_error"])
            largest_chsh = max(largest_chsh, result["chsh_max"])
    print({"worst_norm_error": worst_norm, "largest_chsh": largest_chsh})
    assert worst_norm < 1e-12
    assert largest_chsh <= 2.0 * 2.0**0.5 + 1e-12
