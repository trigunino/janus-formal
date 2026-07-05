"""Shared strict schema constants for active Z2/Sigma BAO manifests."""

FORBIDDEN_FLAGS = [
    "compressed_planck_lcdm_rd_used",
    "archived_z4_reuse_used",
    "phenomenological_holst_bao_scan_used",
]

FORBIDDEN_PROVENANCE_TOKENS = ["demo", "lcdm", "planck", "z4", "holst_scan"]

REQUIRED_COMPONENT_PROVENANCE = [
    "cartan_ghy_rho",
    "cartan_ghy_p",
    "holst_nieh_yan_rho",
    "holst_nieh_yan_p",
    "matter_flux_rho",
    "matter_flux_p",
    "counterterm_rho",
    "counterterm_p",
    "rho_baryon_Z2Sigma",
    "rho_photon_Z2Sigma",
    "Gamma_drag_Z2Sigma",
]
