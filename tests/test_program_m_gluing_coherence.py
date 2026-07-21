import numpy as np
import pytest

from scripts.audit_program_m_gluing_coherence import glue_diagram, run_audit


def test_gluing_coherence_audit_passes() -> None:
    assert all(run_audit()["gates"].values())


def test_disagreement_on_shared_interface_relation_is_rejected() -> None:
    edge = np.array([[False, True], [False, False]], dtype=bool)
    empty = np.zeros((2, 2), dtype=bool)
    interfaces = [((0, 0), (1, 0)), ((0, 1), (1, 1))]
    with pytest.raises(ValueError, match="disagree"):
        glue_diagram([edge, empty], interfaces)
