"""Stability scan for the tuned Hassan-Rosen minisuperspace branch."""

import numpy as np

from hassan_rosen_minisuperspace import effective_coupling, potential
from compare_models import evaluate


if __name__ == "__main__":
    ratios = np.geomspace(0.25, 4.0, 41)
    potentials = [potential(1.0, r) for r in ratios]
    chsh_values = [evaluate(1.0, effective_coupling(r))["chsh_max"] for r in ratios]
    print({
        "min_potential": min(potentials),
        "max_potential": max(potentials),
        "max_chsh": max(chsh_values),
        "quantum_bound": 2.0 * np.sqrt(2.0),
    })
    assert min(potentials) >= -1e-12
    assert max(chsh_values) <= 2.0 * np.sqrt(2.0) + 1e-12
