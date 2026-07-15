from __future__ import annotations

import json
import math
from dataclasses import asdict, dataclass


@dataclass(frozen=True)
class WorldvolumeRGAudit:
    microscopic_inputs_supplied: bool
    sextic_beta: float | None
    pure_scalar_beta: float | None
    mixed_gauge_scalar_beta: float | None
    ll_beta: float | None
    composite_anomalous_dimension: float | None
    sextic_coupling: float | None
    log_coefficient: float | None
    stationary_log: float | None
    locally_stable_one_log_vacuum: bool
    callan_symanzik_residual: float | None
    finite_scheme_residual: float | None
    beta_decomposition_residual: float | None
    beta_decomposition_consistent: bool
    verdict: str


def build_audit(
    *,
    sextic_beta: float | None = None,
    pure_scalar_beta: float | None = None,
    mixed_gauge_scalar_beta: float | None = None,
    ll_beta: float | None = None,
    composite_anomalous_dimension: float | None = None,
    sextic_coupling: float | None = None,
    scheme_shift: float = 0.25,
) -> WorldvolumeRGAudit:
    values = (sextic_beta, composite_anomalous_dimension, sextic_coupling)
    if any(value is None for value in values):
        return WorldvolumeRGAudit(
            microscopic_inputs_supplied=False,
            sextic_beta=sextic_beta,
            pure_scalar_beta=pure_scalar_beta,
            mixed_gauge_scalar_beta=mixed_gauge_scalar_beta,
            ll_beta=ll_beta,
            composite_anomalous_dimension=composite_anomalous_dimension,
            sextic_coupling=sextic_coupling,
            log_coefficient=None,
            stationary_log=None,
            locally_stable_one_log_vacuum=False,
            callan_symanzik_residual=None,
            finite_scheme_residual=None,
            beta_decomposition_residual=None,
            beta_decomposition_consistent=False,
            verdict="blocked_on_microscopic_beta_and_anomalous_dimension",
        )

    beta = float(sextic_beta)
    gamma = float(composite_anomalous_dimension)
    coupling = float(sextic_coupling)
    components = (pure_scalar_beta, mixed_gauge_scalar_beta, ll_beta)
    supplied_components = tuple(value for value in components if value is not None)
    if not all(math.isfinite(float(value)) for value in supplied_components):
        raise ValueError("RG inputs must be finite")
    if not all(math.isfinite(value) for value in (beta, gamma, coupling, scheme_shift)):
        raise ValueError("RG inputs must be finite")

    decomposition_residual = (
        beta - sum(float(value) for value in components if value is not None)
        if all(value is not None for value in components)
        else None
    )
    decomposition_consistent = (
        decomposition_residual is None or abs(decomposition_residual) <= 1.0e-12
    )

    log_coefficient = beta - 3.0 * gamma * coupling
    stationary_log = (
        -(3.0 * coupling + log_coefficient) / (3.0 * log_coefficient)
        if log_coefficient != 0.0
        else None
    )
    shifted_coupling = coupling + log_coefficient * scheme_shift
    shifted_log = (stationary_log - scheme_shift) if stationary_log is not None else None
    scheme_residual = (
        (shifted_coupling + log_coefficient * shifted_log)
        - (coupling + log_coefficient * stationary_log)
        if stationary_log is not None and shifted_log is not None
        else None
    )
    cs_residual = log_coefficient - (beta - 3.0 * gamma * coupling)
    stable = (
        log_coefficient > 0.0
        and stationary_log is not None
        and decomposition_consistent
    )

    return WorldvolumeRGAudit(
        microscopic_inputs_supplied=True,
        sextic_beta=beta,
        pure_scalar_beta=pure_scalar_beta,
        mixed_gauge_scalar_beta=mixed_gauge_scalar_beta,
        ll_beta=ll_beta,
        composite_anomalous_dimension=gamma,
        sextic_coupling=coupling,
        log_coefficient=log_coefficient,
        stationary_log=stationary_log,
        locally_stable_one_log_vacuum=stable,
        callan_symanzik_residual=cs_residual,
        finite_scheme_residual=scheme_residual,
        beta_decomposition_residual=decomposition_residual,
        beta_decomposition_consistent=decomposition_consistent,
        verdict=(
            "conditional_local_one_log_vacuum"
            if stable
            else (
                "inconsistent_beta_sector_decomposition"
                if not decomposition_consistent
                else "no_stable_one_log_vacuum_from_supplied_rg_data"
            )
        ),
    )


def main() -> int:
    print(json.dumps(asdict(build_audit()), indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
