"""Stability scan for the tuned minisuperspace branch."""
import numpy as np
from hassan_rosen_minisuperspace import effective_coupling, potential
from compare_models import evaluate

if __name__ == "__main__":
    ratios = np.geomspace(0.25, 4.0, 41)
    potentials = [potential(1.0, r) for r in ratios]
    chsh = [evaluate(1.0, effective_coupling(r))["chsh_max"] for r in ratios]
    bound = 2.0 * np.sqrt(2.0)
    print({"min_potential": min(potentials), "max_chsh": max(chsh), "bound": bound})
    assert min(potentials) >= -1e-12
    assert max(chsh) <= bound + 1e-12
