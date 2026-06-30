from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_integrability_first_phi_l_selection.md")
JSON_PATH = Path("outputs/reports/p0_integrability_first_phi_l_selection.json")


def build_payload() -> dict:
    route = {
        "object": "select phi and L from dust-image curl, Frobenius, and inverse-map conditions",
        "not_object": "do not select phi/L by tuning S_couple or observational residuals",
        "target": (
            "derive an admissible cross-sector map whose dust image has closed curls, "
            "continuous B_4vol, mirror inverse data, and the same phi/L Cuu bridge"
        ),
    }
    conditions = [
        {
            "name": "dust_image_curl",
            "condition": "curl(dust image one-form[phi,L])=0 on the single-stream image distribution",
            "role": "Frobenius gate for local map compatibility",
            "status": "necessary-not-sufficient",
        },
        {
            "name": "frobenius_inverse_map",
            "condition": "D_[mu D_nu] phi and D_[mu D_nu] L close with phi^{-1}, L^{-1} mirrors",
            "role": "blocks independent plus/minus fits",
            "status": "open",
        },
        {
            "name": "b4vol_continuity",
            "condition": "B_4vol remains continuous and inverse-multiplies across the mirror map",
            "role": "prevents measure jumps at sector matching",
            "status": "required",
        },
        {
            "name": "same_phi_l_cuu_bridge",
            "condition": "the same phi/L used for integrability must generate the Cuu bridge",
            "role": "prevents a separate optical/source map",
            "status": "required",
        },
        {
            "name": "caustic_multistream_obstruction",
            "condition": "det dphi=0 or multi-stream dust images break single inverse-map selection",
            "role": "limits the route to regular patches or sheeted extensions",
            "status": "obstruction",
        },
    ]
    uniqueness = {
        "forces_unique_phi_l": False,
        "unique_only_if": (
            "curl/Frobenius equations plus boundary or initial data fix a single regular "
            "inverse map modulo admissible gauge"
        ),
        "reason": (
            "Integrability removes incompatible maps but generally leaves homogeneous, "
            "holonomy, gauge, and boundary-data freedom."
        ),
    }
    closure_tests = [
        "prove dust-image curls vanish from source equations, not S_couple choice",
        "impose phi o phi^{-1}=id and L^{-1} mirror consistency in both sectors",
        "check B_4vol continuity and inverse determinant relation through the map",
        "reuse the identical phi/L in hE=rho hCuu and optical Cuu substitutions",
        "exclude caustic or multistream patches, or define a sheeted inverse-map rule",
    ]
    return {
        "description": "Bounded P0 artifact for integrability-first phi/L selection.",
        "status": "source-compatible-integrability-first-route-open",
        "selection_source": "dust_image_curl_frobenius_inverse_map",
        "uses_s_couple_selection": False,
        "source_compatible": True,
        "physics_closed": False,
        "prediction_ready": False,
        "fit_to_observations": False,
        "free_parameters": [],
        "route": route,
        "conditions": conditions,
        "uniqueness": uniqueness,
        "closure_tests": closure_tests,
        "verdict": (
            "The integrability-first route is source-compatible and may target phi/L "
            "without S_couple tuning, but it is not yet closed. It does not force a "
            "unique phi/L unless the curl/Frobenius conditions plus boundary data fix "
            "the inverse map. Caustics and multistream dust remain obstructions, so "
            "the artifact is not prediction-ready."
        ),
    }


def render_markdown(payload: dict) -> str:
    route = payload["route"]
    uniqueness = payload["uniqueness"]
    lines = [
        "# P0 Integrability-First Phi/L Selection",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Selection source: {payload['selection_source']}",
        f"Uses S_couple selection: {payload['uses_s_couple_selection']}",
        f"Source compatible: {payload['source_compatible']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        f"Fit to observations: {payload['fit_to_observations']}",
        f"Free parameters: {payload['free_parameters']}",
        "",
        "## Route",
        "",
        f"- Object: {route['object']}",
        f"- Not object: {route['not_object']}",
        f"- Target: {route['target']}",
        "",
        "## Conditions",
        "",
    ]
    for row in payload["conditions"]:
        lines.append(f"- {row['name']}: {row['condition']} (status={row['status']})")
        lines.append(f"  - role: {row['role']}")
    lines.extend(
        [
            "",
            "## Uniqueness",
            "",
            f"Forces unique phi/L: {uniqueness['forces_unique_phi_l']}",
            f"Unique only if: {uniqueness['unique_only_if']}",
            f"Reason: {uniqueness['reason']}",
            "",
            "## Closure Tests",
            "",
        ]
    )
    lines.extend(f"- {item}" for item in payload["closure_tests"])
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
