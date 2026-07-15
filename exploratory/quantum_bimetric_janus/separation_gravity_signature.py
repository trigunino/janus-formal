"""Phenomenological separation and gravity-potential scan."""
import numpy as np
from compare_models import evaluate
from hassan_rosen_minisuperspace import effective_coupling

def janus_coupling(r, distance, phi, length_scale=2.0, gravity_scale=0.5):
    return effective_coupling(r)*np.exp(-distance/length_scale)*(1+gravity_scale*phi)

if __name__ == "__main__":
    for distance, phi in ((0,0),(1,0),(2,0),(1,0.2),(1,-0.2)):
        coupling = janus_coupling(1.5, distance, phi)
        print(distance, phi, coupling, evaluate(1.0, coupling))
