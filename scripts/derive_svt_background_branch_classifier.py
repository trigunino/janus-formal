from __future__ import annotations

from pathlib import Path
import json
import os

import sympy as sp

try:
    from scripts.derive_svt_quadratic_coefficients import (
        MHR2,
        MPL2,
        TENSION,
        VEV,
        expr_text,
    )
    from scripts.derive_svt_cartan_spin_connection_and_background import (
        background_balance_residual,
        required_tension_for_minkowski,
    )
except ModuleNotFoundError:  # pragma: no cover - direct script execution
    from derive_svt_quadratic_coefficients import (
        MHR2,
        MPL2,
        TENSION,
        VEV,
        expr_text,
    )
    from derive_svt_cartan_spin_connection_and_background import (
        background_balance_residual,
        required_tension_for_minkowski,
    )


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))
REPORT_PATH = REPORT_DIR / "svt_background_branch_classifier.md"
JSON_PATH = REPORT_DIR / "svt_background_branch_classifier.json"


def tensor_stability_bound() -> sp.Expr:
    return sp.factor(MPL2 * MHR2 * (3 * VEV**2 + 3 * VEV + 1))


def tensor_stability_margin() -> sp.Expr:
    return sp.factor(TENSION - tensor_stability_bound())


def minkowski_margin_after_balance() -> sp.Expr:
    return sp.factor(
        required_tension_for_minkowski().subs(TENSION, required_tension_for_minkowski())
        - tensor_stability_bound()
    )


def witness(values: dict[sp.Symbol, sp.Expr]) -> dict:
    residual = sp.factor(background_balance_residual().subs(values))
    margin = sp.factor(tensor_stability_margin().subs(values))
    return {
        "values": {
            "v": str(values[VEV]),
            "mHR2": str(values[MHR2]),
            "Mpl2": str(values[MPL2]),
            "membraneTension": str(values[TENSION]),
        },
        "background_residual": expr_text(residual),
        "minkowski_balanced": residual == 0,
        "tensor_stability_margin": expr_text(margin),
        "tensor_stable_strict": bool(margin > 0),
        "branch": "minkowski" if residual == 0 else "curved_background",
    }


def build_payload() -> dict:
    m1_mpl4_margin = sp.factor(
        minkowski_margin_after_balance().subs({MHR2: 1, MPL2: 4})
    )
    return {
        "artifact": "svt_background_branch_classifier",
        "status": "minkowski_static_branch_conflicts_with_tensor_bound_for_checked_witnesses",
        "fit_used": False,
        "free_parameters_fitted_to_data": [],
        "equations": {
            "minkowski_required_T_memb": expr_text(required_tension_for_minkowski()),
            "tensor_stability_bound": expr_text(tensor_stability_bound()),
            "tensor_stability_margin": expr_text(tensor_stability_margin()),
            "minkowski_margin_after_balance": expr_text(minkowski_margin_after_balance()),
            "minkowski_margin_mHR2_1_Mpl2_4": expr_text(m1_mpl4_margin),
        },
        "witnesses": {
            "old_T30_v1_m1_Mpl4": witness({VEV: 1, MHR2: 1, MPL2: 4, TENSION: 30}),
            "minkowski_T6_v1_m1_Mpl4": witness({VEV: 1, MHR2: 1, MPL2: 4, TENSION: 6}),
            "weak_mHR_T06_v1_m01_Mpl4": witness(
                {VEV: 1, MHR2: sp.Rational(1, 10), MPL2: 4, TENSION: sp.Rational(3, 5)}
            ),
        },
        "verdict": {
            "T30_is_tensor_stable": True,
            "T30_is_minkowski": False,
            "T6_is_minkowski": True,
            "T6_is_tensor_stable": False,
            "non_minkowski_branch_can_pass_tensor_bound": True,
            "prediction_ready": False,
            "reason": (
                "T_memb=30 can be a curved-background branch candidate, but the "
                "SVT action used here was derived on the flat Minkowski branch."
            ),
        },
        "needed_inputs": [
            "curved-background SVT quadratic action for the T_memb=30 branch",
            "mapping of residual background tension to an effective Hubble/curvature scale",
            "recomputed no-ghost/no-gradient bounds on that curved branch",
        ],
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# SVT Background Branch Classifier",
        "",
        f"Status: `{payload['status']}`",
        f"Fit used: `{payload['fit_used']}`",
        f"Prediction ready: `{payload['verdict']['prediction_ready']}`",
        "",
        "## Equations",
    ]
    for key, value in payload["equations"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Witnesses"])
    for key, value in payload["witnesses"].items():
        lines.append(
            f"- {key}: branch `{value['branch']}`, residual `{value['background_residual']}`, "
            f"tensor margin `{value['tensor_stability_margin']}`"
        )
    lines.extend(["", "## Needed Inputs"])
    lines.extend(f"- {item}" for item in payload["needed_inputs"])
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    payload = build_payload()
    report_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
