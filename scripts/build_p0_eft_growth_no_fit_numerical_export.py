from __future__ import annotations

from pathlib import Path
import csv
import json
import math


REPORT_PATH = Path("outputs/reports/p0_eft_growth_no_fit_numerical_export.md")
JSON_PATH = Path("outputs/reports/p0_eft_growth_no_fit_numerical_export.json")
CSV_PATH = Path("outputs/reports/p0_eft_growth_no_fit_curve.csv")


def rk4_step(state: tuple[float, float], x: float, dx: float, rhs) -> tuple[float, float]:
    def add(s: tuple[float, float], k: tuple[float, float], scale: float) -> tuple[float, float]:
        return s[0] + scale * k[0], s[1] + scale * k[1]

    k1 = rhs(x, state)
    k2 = rhs(x + dx / 2, add(state, k1, dx / 2))
    k3 = rhs(x + dx / 2, add(state, k2, dx / 2))
    k4 = rhs(x + dx, add(state, k3, dx))
    return (
        state[0] + dx * (k1[0] + 2 * k2[0] + 2 * k3[0] + k4[0]) / 6,
        state[1] + dx * (k1[1] + 2 * k2[1] + 2 * k3[1] + k4[1]) / 6,
    )


def branch_constants(
    mpl2: float = 4.0,
    eps: float = 1.0,
    h2: float = 0.5,
    rho_ds: float | None = None,
) -> dict:
    gamma = 1.0 / math.sqrt(6.0)
    rho = rho_ds if rho_ds is not None else 3.0 * mpl2 * h2
    ratio = eps / (mpl2 * gamma)
    if abs(ratio) >= 1:
        raise ValueError("|eps| must be below Mpl2/sqrt(6)")
    chi_inf = 2.0 * math.atanh(ratio) / gamma
    lambda_j = rho / (math.cosh(gamma * chi_inf) - 1.0)
    j_bg = eps * rho / mpl2
    return {
        "Mpl2": mpl2,
        "eps": eps,
        "H2": h2,
        "H": math.sqrt(h2),
        "gamma": gamma,
        "rho_dS_residual": rho,
        "ratio": ratio,
        "chi_inf": chi_inf,
        "Lambda_J": lambda_j,
        "J_bg": j_bg,
        "existence_bound_satisfied": abs(ratio) < 1,
    }


def integrate_radion(constants: dict, *, a_min: float = 0.02, a_sigma: float = 0.5, a_max: float = 1.0) -> list[dict]:
    h2 = constants["H2"]
    gamma = constants["gamma"]
    lambda_j = constants["Lambda_J"]
    j_bg = constants["J_bg"]
    mpl2 = constants["Mpl2"]
    q_a = 1.0 / math.sqrt(6.0)
    q_t = 1.0
    kick = constants["eps"] * (4.0 * q_t - 2.0 * q_a) / (h2 * a_sigma * a_sigma)
    x0 = math.log(a_min)
    xs = math.log(a_sigma)
    x1 = math.log(a_max)
    n = 360
    dx = (x1 - x0) / n
    state = (0.0, 0.0)
    rows: list[dict] = []
    kicked = False

    def rhs(_: float, s: tuple[float, float]) -> tuple[float, float]:
        chi, chix = s
        d_v_eff = lambda_j * gamma * math.sinh(gamma * chi) - j_bg
        return chix, -3.0 * chix - d_v_eff / h2

    x = x0
    for _ in range(n + 1):
        if not kicked and x >= xs:
            state = (state[0], state[1] + kick)
            kicked = True
        a = math.exp(x)
        omega_t = state[1] * state[1] / (3.0 * mpl2)
        rows.append({"a": a, "x": x, "chi": state[0], "chi_x": state[1], "Omega_T": omega_t})
        if x < x1:
            state = rk4_step(state, x, dx, rhs)
            x += dx
    return rows


def derived_omega_m0(constants: dict, radion_rows: list[dict]) -> float:
    omega_t0 = radion_rows[-1]["Omega_T"]
    omega_ds = constants["rho_dS_residual"] / (3.0 * constants["Mpl2"] * constants["H2"])
    return 1.0 - omega_ds - omega_t0


def integrate_growth(
    constants: dict,
    radion_rows: list[dict],
    *,
    k: float = 1.0,
    omega_m0: float | None = None,
    delta_initial: float = 1.0e-3,
    growth_slope_initial: float = 1.0,
) -> list[dict]:
    h2 = constants["H2"]
    coeff = 161.0 / 36.0
    delta = delta_initial
    ddelta = growth_slope_initial * delta_initial
    growth_rows: list[dict] = []
    previous_x = radion_rows[0]["x"]
    omega_m0_value = derived_omega_m0(constants, radion_rows) if omega_m0 is None else omega_m0

    def omega_m(a: float) -> float:
        return omega_m0_value * a ** -3 / (omega_m0_value * a ** -3 + (1 - omega_m0_value))

    for row in radion_rows:
        x = row["x"]
        dx = x - previous_x
        previous_x = x
        if dx:
            om_t = row["Omega_T"]
            mu = 1.0 + coeff * om_t * k * k / (k * k + 1.5 * h2)

            def rhs(xx: float, s: tuple[float, float]) -> tuple[float, float]:
                aa = math.exp(xx)
                return s[1], -2.0 * s[1] + 1.5 * omega_m(aa) * mu * s[0]

            delta, ddelta = rk4_step((delta, ddelta), x - dx, dx, rhs)
        f = ddelta / delta if delta != 0 else float("nan")
        growth_rows.append({**row, "mu": 1.0 + coeff * row["Omega_T"] * k * k / (k * k + 1.5 * h2), "delta": delta, "f": f})
    today_delta = growth_rows[-1]["delta"]
    for row in growth_rows:
        row["fsigma8_shape"] = row["f"] * row["delta"] / today_delta
    return growth_rows


def build_payload() -> dict:
    constants = branch_constants()
    radion = integrate_radion(constants)
    growth = integrate_growth(constants, radion)
    omega_m0 = derived_omega_m0(constants, radion)
    sample = [growth[0], growth[len(growth) // 2], growth[-1]]
    theorem_status = {
        "orientation_units_selected_for_numeric_branch": True,
        "atanh_domain_checked": constants["existence_bound_satisfied"],
        "chi_inf_numeric_exported": True,
        "Lambda_J_numeric_exported": True,
        "Omega_T_profile_generated": True,
        "growth_curve_generated": True,
        "Omega_m0_derived_from_Friedmann_branch": True,
        "positive_matter_branch": omega_m0 > 0,
        "fsigma8_prediction_no_fit_ready_conditionally": True,
        "full_cosmology_prediction_ready": omega_m0 > 0,
    }
    return {
        "description": "Conditional no-fit numerical export for the EC Janus growth branch.",
        "status": "conditional-no-fit-growth-curve-generated",
        "constants": constants,
        "Omega_m0": omega_m0,
        "samples": sample,
        "theorem_status": theorem_status,
        "risk": (
            "The curve is conditional on eps=+1, Mpl2=4 and H2=1/2. Omega_m0 is derived "
            "from the branch Friedmann budget, so branch positivity is the relevant check."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Growth No-Fit Numerical Export",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        "",
        "## Constants",
    ]
    lines.extend(f"- {key}: {value}" for key, value in payload["constants"].items())
    lines.append(f"- Omega_m0: {payload['Omega_m0']}")
    lines.extend(["", "## Status"])
    lines.extend(f"- {key}: {value}" for key, value in payload["theorem_status"].items())
    lines.extend(["", "## Samples"])
    for row in payload["samples"]:
        lines.append(
            f"- a={row['a']:.6g}, chi={row['chi']:.6g}, Omega_T={row['Omega_T']:.6g}, "
            f"mu={row['mu']:.6g}, fsigma8_shape={row['fsigma8_shape']:.6g}"
        )
    lines.extend(["", f"Risk: {payload['risk']}", ""])
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH, csv_path: Path = CSV_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    rows = integrate_growth(payload["constants"], integrate_radion(payload["constants"]))
    with csv_path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")
    print(f"Wrote {CSV_PATH}")


if __name__ == "__main__":
    main()
