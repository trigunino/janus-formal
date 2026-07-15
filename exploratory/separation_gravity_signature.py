"""Toy test of separation and external gravitational-potential dependence."""

import numpy as np

from compare_models import evaluate
from hassan_rosen_minisuperspace import effective_coupling


def janus_coupling(r: float, distance: float, potential: float,
                   length_scale: float = 2.0, gravity_scale: float = 0.5) -> float:
    """Phenomenological propagation ansatz; not yet derived covariantly."""
    base = effective_coupling(r)
    return base * np.exp(-distance / length_scale) * (1.0 + gravity_scale * potential)


if __name__ == "__main__":
    print("distance phi coupling concurrence chsh_max")
    for distance, phi in ((0.0, 0.0), (1.0, 0.0), (2.0, 0.0), (1.0, 0.2), (1.0, -0.2)):
        coupling = janus_coupling(1.5, distance, phi)
        result = evaluate(omega_minus=1.0, coupling=coupling)
        print(f"{distance:8.2f} {phi:5.2f} {coupling:8.6f} {result['concurrence']:11.6f} {result['chsh_max']:8.6f}")
