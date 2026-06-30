from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/temporary_scaffolds_audit.md")
JSON_PATH = Path("outputs/reports/temporary_scaffolds_audit.json")


def build_payload() -> dict:
    items = [
        {
            "item": "demo PM initial state and velocity pattern",
            "status": "replaced in absolute-shear pipeline",
            "replacement": "legacy diagnostics only; use bounded/source-derived IC pipeline for observable chain",
            "blocks_final_claim": False,
        },
        {
            "item": "prototype bounded Gaussian IC",
            "status": "partially controlled by analytic multimode convergence IC",
            "replacement": "source-derived Janus transfer function, amplitude and velocity field",
            "blocks_final_claim": True,
        },
        {
            "item": "Q_det positive-effective density convention",
            "status": "working convention",
            "replacement": "tensor metric-volume mapping between positive and negative source measures",
            "blocks_final_claim": True,
        },
        {
            "item": "Q_cross equal-projection and local velocity bridge",
            "status": "working derivation",
            "replacement": "global L_minus_to_plus tetrad/covector projection for negative-sector stress along positive null rays",
            "blocks_final_claim": True,
        },
        {
            "item": "standard weak-lensing prefactor unity branch",
            "status": "scaffold",
            "replacement": "proved Janus tensor normalization factors Q_source,Q_det,Q_cross,Q_proj,Q_dist",
            "blocks_final_claim": True,
        },
        {
            "item": "diagnostic source redshift distribution",
            "status": "temporary",
            "replacement": "declared survey n(z) and tomographic bins",
            "blocks_final_claim": True,
        },
        {
            "item": "standard E-mode shear screen relation",
            "status": "scaffold",
            "replacement": "proof that Janus optical screen reduces to the same weak-shear operator",
            "blocks_final_claim": True,
        },
        {
            "item": "no survey likelihood",
            "status": "missing final layer",
            "replacement": "observed data vector, covariance, mask/window treatment, and no-fit comparison rule",
            "blocks_final_claim": True,
        },
        {
            "item": "small-grid 64^3 observable diagnostic",
            "status": "replaced by 175^3 admissible run plus 128->175 convergence diagnostic",
            "replacement": "continue convergence beyond 175^3 when feasible",
            "blocks_final_claim": True,
        },
        {
            "item": "H0^-1 PM time calibration",
            "status": "working calibration",
            "replacement": "replace only if full Janus PM equations derive a different code time variable",
            "blocks_final_claim": False,
        },
        {
            "item": "factorized C_J normalization map",
            "status": "keeper",
            "replacement": "not replaced; fill factors with source-derived values",
            "blocks_final_claim": False,
        },
    ]
    return {
        "description": "Audit of temporary scaffolds versus working Janus calibration layers.",
        "temporary_count": sum(1 for item in items if item["blocks_final_claim"]),
        "keeper_count": sum(1 for item in items if not item["blocks_final_claim"]),
        "items": items,
        "verdict": (
            "Do not present current PM/lensing outputs as final evidence. They are useful "
            "because each temporary layer is isolated and has a named replacement."
        ),
    }


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Temporary Scaffolds Audit",
        "",
        payload["description"],
        "",
        "| item | status | replacement | blocks final claim |",
        "|---|---|---|---|",
    ]
    for item in payload["items"]:
        lines.append(
            f"| {item['item']} | {item['status']} | {item['replacement']} | "
            f"{item['blocks_final_claim']} |"
        )
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
