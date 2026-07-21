import numpy as np
import pytest

from scripts.audit_program_m_interface_gluing import glue_relations, run_audit


def test_free_interface_gluing_audit_passes() -> None:
    assert all(run_audit()["gates"].values())


def test_incompatible_interface_is_rejected() -> None:
    left = np.array([[False]], dtype=bool)
    right = np.array([[True]], dtype=bool)
    with pytest.raises(ValueError, match="disagree"):
        glue_relations(left, right, (0,), (0,))
