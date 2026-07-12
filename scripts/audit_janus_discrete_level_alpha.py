from __future__ import annotations

import json
import math
from dataclasses import asdict, dataclass


@dataclass(frozen=True)
class LevelCandidate:
    lock_constant: float
    target_continuous_level: float
    nearest_level: int
    predicted_alpha_m: float
    relative_radius_error: float
    required_lambda_over_beta: float


@dataclass(frozen=True)
class DiscreteLevelAudit:
    target_alpha_m: float
    uv_length_m: float
    target_hierarchy_exponent: float
    candidates: list[LevelCandidate]
    conclusion: str


def build_audit(
    target_alpha_m: float = 1.0e26,
    uv_length_m: float = 1.616255e-35,
    lock_constants: tuple[float, ...] = (1.0, 2.0, 4.0, 8.0),
) -> DiscreteLevelAudit:
    if target_alpha_m <= 0.0 or uv_length_m <= 0.0:
        raise ValueError("lengths must be positive")
    exponent = math.log(2.0 * target_alpha_m / uv_length_m)
    candidates: list[LevelCandidate] = []
    for c_lock in lock_constants:
        if c_lock <= 0.0:
            raise ValueError("lock constants must be positive")
        k_continuous = c_lock * exponent / (8.0 * math.pi**2)
        k = max(1, int(round(k_continuous)))
        x_k = 8.0 * math.pi**2 * k / c_lock
        alpha_k = 0.5 * uv_length_m * math.exp(x_k)
        relative_error = alpha_k / target_alpha_m - 1.0
        lambda_over_beta = (24.0 * math.pi**2 * k / c_lock - 1.0) / 3.0
        candidates.append(
            LevelCandidate(
                lock_constant=c_lock,
                target_continuous_level=k_continuous,
                nearest_level=k,
                predicted_alpha_m=alpha_k,
                relative_radius_error=relative_error,
                required_lambda_over_beta=lambda_over_beta,
            )
        )
    return DiscreteLevelAudit(
        target_alpha_m=target_alpha_m,
        uv_length_m=uv_length_m,
        target_hierarchy_exponent=exponent,
        candidates=candidates,
        conclusion=(
            "An integer level makes alpha discrete. A sparse level spectrum is "
            "generally too coarse to hit a target radius unless the computed "
            "lock constant or additional matter data refine the spacing; this "
            "is a falsifiable output, not a parameter fit."
        ),
    )


def main() -> int:
    print(json.dumps(asdict(build_audit()), indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
