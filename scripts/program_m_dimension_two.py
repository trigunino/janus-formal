"""Polynomial certificate algorithm for Dushnik--Miller dimension at most two."""

from __future__ import annotations

from collections import deque

import numpy as np


def _is_transitive_orientation(adjacency: np.ndarray, orientation: np.ndarray) -> bool:
    if not np.array_equal(orientation | orientation.T, adjacency):
        return False
    if np.any(orientation & orientation.T):
        return False
    paths_two = orientation.astype(int) @ orientation.astype(int) > 0
    return bool(np.all(~paths_two | orientation))


def transitive_orientation(adjacency: np.ndarray) -> np.ndarray | None:
    """Greedy implication-class orientation of a finite comparability graph.

    This is a direct matrix implementation of the implication-class algorithm
    described by Golumbic and in Sage's comparability-graph documentation.
    Runtime is polynomial; the returned orientation is always verified.
    """
    graph = np.asarray(adjacency, dtype=bool).copy()
    np.fill_diagonal(graph, False)
    if not np.array_equal(graph, graph.T):
        raise ValueError("adjacency must be symmetric")
    original = graph.copy()
    orientation = np.zeros_like(graph)

    while np.any(graph):
        left, right = np.argwhere(np.triu(graph, 1))[0]
        implication_class: set[tuple[int, int]] = set()
        queue: deque[tuple[int, int]] = deque([(int(left), int(right))])
        contradictory = False
        while queue and not contradictory:
            source, target = queue.popleft()
            if (target, source) in implication_class:
                contradictory = True
                break
            if (source, target) in implication_class:
                continue
            implication_class.add((source, target))

            # Edges sharing `source` whose other endpoints are nonadjacent must
            # both leave (or both enter) that common endpoint.
            for other in np.flatnonzero(graph[source]):
                other = int(other)
                if other != target and not graph[target, other]:
                    queue.append((source, other))

            # The same condition for edges sharing `target`.
            for other in np.flatnonzero(graph[target]):
                other = int(other)
                if other != source and not graph[source, other]:
                    queue.append((other, target))

        if contradictory:
            return None
        for source, target in implication_class:
            if not graph[source, target] or orientation[target, source]:
                return None
            orientation[source, target] = True
            graph[source, target] = False
            graph[target, source] = False

    return orientation if _is_transitive_orientation(original, orientation) else None


def _total_order_permutation(relation: np.ndarray) -> tuple[int, ...] | None:
    size = len(relation)
    if not np.all(np.diag(relation)):
        return None
    if not np.all(relation | relation.T):
        return None
    if np.any((relation & relation.T) & ~np.eye(size, dtype=bool)):
        return None
    if not np.all((relation.astype(int) @ relation.astype(int) == 0) | relation):
        return None
    predecessors = np.count_nonzero(relation, axis=0) - 1
    permutation = tuple(np.argsort(predecessors).tolist())
    return permutation


def polynomial_two_order_realizer(
    order: np.ndarray,
) -> tuple[tuple[int, ...], tuple[int, ...]] | None:
    """Return two linear extensions whose intersection is `order`, if they exist."""
    poset = np.asarray(order, dtype=bool)
    size = len(poset)
    distinct = ~np.eye(size, dtype=bool)
    incomparable = distinct & ~poset & ~poset.T
    conjugate_orientation = transitive_orientation(incomparable)
    if conjugate_orientation is None:
        return None

    strict_poset = poset & distinct
    first_relation = np.eye(size, dtype=bool) | strict_poset | conjugate_orientation
    second_relation = np.eye(size, dtype=bool) | strict_poset | conjugate_orientation.T
    first = _total_order_permutation(first_relation)
    second = _total_order_permutation(second_relation)
    if first is None or second is None:
        return None

    try:
        from scripts.audit_program_m_two_order_representation import linear_order_matrix
    except ModuleNotFoundError:  # Direct execution from the scripts directory.
        from audit_program_m_two_order_representation import linear_order_matrix

    if not np.array_equal(
        linear_order_matrix(first) & linear_order_matrix(second), poset
    ):
        return None
    return first, second
