"""Lapse constraint and local stability checks."""
from hassan_rosen_minisuperspace import potential

def lapse_constraint(r, h=1e-6):
    return (potential(1+h, r) - potential(1-h, r))/(2*h)

def radial_hessian(r=1.0, h=1e-4):
    return (potential(1, r+h) - 2*potential(1, r) + potential(1, r-h))/(h*h)

if __name__ == "__main__":
    constraint = lapse_constraint(1.0)
    hessian = radial_hessian()
    print({"lapse_constraint": constraint, "radial_hessian": hessian})
    assert abs(constraint) < 1e-8
    assert hessian > 0
