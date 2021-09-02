"""A module for a class for finite translation quiver.

In this module, we define a class `TranslationQuiver`,
which is a class for finite translation quiver.
For a TranslationQuiver object, there are some methods
to compute various things.
We often identify a translation quiver and a certain kind of additive category,
see the docstring of `TranslationQuiver`.

References:
    [Iy1] O. Iyama, tau-categories I: Ladders,
        Algebr. Represent. Theory 8 (2005), no. 3, 297–321.

    [Iy2] O. Iyama, tau-categories II:
        Nakayama pairs and Rejective subcategories,
        Algebr. Represent. Theory 8 (2005), no. 4, 449–477.

    [Iy3] O. Iyama, The relationship between homological properties
        and representation theoretic realization of artin algebras,
        Trans. Amer. Math. Soc. 357 (2005), no. 2, 709–734.

    [INP] O. Iyama, H. Nakaoka, Y. Palu,
        Auslander-Reiten theory in extriangulated categories, arXiv:1805.03776.
"""

from __future__ import annotations
from collections.abc import Hashable, Callable
from math import lcm
from typing import Counter

Q = Hashable  # Type for vertices
NQ = list[Q]
# Type for non-negative formal combination of vertices
# represented by lists of vertices,
# and for objects in our category (by taking direct sums).


def substract(lst1: list[Q], lst2: list[Q]) -> list[Q]:
    """Compute the positive part of `lst1` - `lst2`.

    We regard `lst1` and `lst2` as an element of some free abelian monoid.
    Then this function computes the "positive part" of
    the substraction `lst1` - `lst2`.

    This function will be used when these lists are lists of vertices.

    Args:
        lst1 (list): A list (of vertices)
        lst2 (list): A list (of vertices)

    Returns:
        list: The result of the computation,
            more precisely, the result is obtained by removing each element
            of `lst2` from `lst1` if it is in `lst1`.
    """
    result = lst1[:]
    for x in lst2:
        if x in result:
            result.remove(x)
    return result


def maximal_cliques(neighbor: dict[Q, list[Q]]) -> list[list[Q]]:
    """Search maximal cliques in a graph using Bron-Kerbosch algorithm.
    Will be used to search maximal orthogonal objects,
    e.g. tau-tilting, n-cluster-tilting, etc.,

    Args:
        neighbor (dict[Q, list[Q]]): Dictionary of neighbor.
            We assume this is simple graph, namely, v not in neighbor[v].

    Returns:
        list[list[Q]]: The list of all maximal cliques.
    """
    all_vertices = list(neighbor.keys())

    def BronKerbosch(clique: list[Q], candidates: list[Q], excluded: list[Q]):
        if not candidates and not excluded:
            yield clique
        elif not candidates:
            return
        else:
            pivot = candidates[0]
            search = [x for x in candidates if x not in neighbor[pivot]]
            # search = candidates[:]
            for v in search:
                new_candidates = [x for x in candidates if x in neighbor[v]]
                new_excluded = [x for x in excluded if x in neighbor[v]]
                yield from BronKerbosch(clique + [v],
                                        new_candidates,
                                        new_excluded)
                candidates.remove(v)
                excluded.append(v)

    return list(BronKerbosch([], all_vertices, []))


def cliques(neighbor: dict[Q, list[Q]]) -> list[list[Q]]:
    """Search all cliques in a graph using (variant of) Bron-Kerbosch algorithm.
    Will be used to search self-orthogonal objects,
    e.g. semibricks, rigid modules, etc.

    Args:
        neighbor (dict[Q, list[Q]]): Dictionary of neighbor.
            We assume this is simple graph, namely, v not in neighbor[v].

    Returns:
        list[list[Q]]: The list of all maximal cliques.
    """
    all_vertices = list(neighbor.keys())

    def BK_modified(clique: list[Q], candidates: list[Q], excluded: list[Q]):
        # print(f"{clique}, {candidates}, {excluded}")
        yield clique
        if not candidates:
            return
        else:
            search = candidates[:]
            for v in search:
                new_candidates = [x for x in candidates if x in neighbor[v]]
                new_excluded = [x for x in excluded if x in neighbor[v]]
                yield from BK_modified(clique + [v],
                                       new_candidates,
                                       new_excluded)
                candidates.remove(v)
                excluded.append(v)

    return list(BK_modified([], all_vertices, []))


class TranslationQuiver():
    """A class of finite translation quivers.

    We assume that the inputted quiver is the AR quiver of
    either of the following classes of categories:
    (Case 1) tau-categories.
    (Case 2) Extriangulated categories with AR conflations.
    When you create a TranslationQuiver object,
    we ask that which case your category is (default: Case 1).
    Note that any translation quiver can be realized as the AR quiver
    of some tau-category, hence there's no restriction on the input.

    --- Details on the AR quiver of categories ---

    Let C be a Krull-Schmidt category with only finitely many
    indecomposables up to isomorphism.
    Suppose that C has sink and source maps. For example, this is satisfied if
    C is Hom-finite over a field.
    Then we can define a finite Auslander-Reiten (valued) quiver of C
    (see e.g. [Definition 2.15, INP]).
    For simplicity, we assume that this is actually a usual non-valued quiver.
    (This is satisfied if C is Hom-finite over an algebraically closed field,
    or more generally, the division ring End_C(M)/rad End_C(M)
    for indecomposable object M does not depend on M.)

    The AR quiver of C may not have natural "translations",
    but if we assume either of the following, then it does have:
    (Case 1) C is a tau-category.
    (Case 2) C is an extriangulated category with AR conflations.
    1 only concerns with the additive structure of C,
    while 2 also concerns with the extra structure (str. of ET cat).

    1. See [Iy1] and [Iy3] for the definition and details of tau-categories.
    In this case, so-called tau-sequences induce the translation structure.
    For example, the following categories are tau-categories.
    - mod A for a finite-dimensional k-algebra.
    - Torsion classes (or torsion-free classes) of mod A.
    - A Hom-finite triangulated category with Serre functor.
    - The ideal quotient of tau-categories by an additive subcategory.
    See e.g. [Example 7.3, Theorem 7.4, INP] for further examples.

    2. See [INP] for the AR theory of extriangulated categories.
    For example, if C is Hom-finite over a field, then C has AR conflations.
    In this case, so-called AR conflations induce the translation structure.
    [INP] proved that the stable category of C is a tau-category
    (under some mild conditions), thus 2 is related to 1 in this way.

    --- Difference between (Case 1) and (Case 2) ---

    For (Case 1), the AR quiver of a tau-category well describes the additive
    structure of the original category.
    For example, one can calculate the dimension of Hom, or more strongly,
    one can compute the radical series of Hom functors.

    For (Case 2), one cannot except such a calculation,
    since the additive structure cannot be approximated by the AR quiver.
    However, by taking the stable category, one may still compute
    Ext^1, stable Hom, and so on.

    Thus some methods below are only allowed for (Case 1).

    --- Type hints ---

    We use the following two types frequently in type hints:
        Q: A type for vertices. This is an allias of Hashable.
        NQ:= list[Q]: A type for formal sum of vertices, or more precisely,
            elements of the free abelian monoid generated by vertices.
            For example, [X, X] represents X + X,
            [X, X, Y, Z] represents 2X + Y + Z.
            It's also used to represent an object in our category.
            For example, [X, X, Y, Z] represents X^2 oplus Y oplus Z.
    """

    def __init__(self,
                 vertices: tuple[Q, ...],
                 arrows: tuple[tuple[Q, Q], ...],
                 tau: dict[Q, Q],
                 is_tau_category: bool = True) -> None:
        """Initialize a translation quiver by inputs.

        Args:
            vertices: The tuple of vertices.
                Each vertex should be hashable, e.g. shouldn't be a list,
                because we use Counter() for list of vertices.
            arrows: The tuple of arrows.
                each arrow is a tuple of the form (`source`, `target`)
                with `source`, `target` in `vertices`.
            tau: A dictionary of AR translation.
            is_tau_category: Whether the considered category is a tau-category
                (Case 1). Default: True.

        Raises:
            ValueError: If it doesn't satisfy the axiom of
                the translation quiver.
        """
        self.vertices = vertices
        self.arrows = arrows
        self.tau = tau
        self.tau_inv = {v: k for k, v in tau.items()}
        # the dictionary of tau^{-1}
        self.is_tau_category = is_tau_category

        # Check whether the constructed data is actually a translation quiver.
        # First check that tau is a partial injection
        if len(self.tau) != len(self.tau_inv):
            raise ValueError("tau is not injective")
        # Next check whether it satisfies the axiom of translation quiver
        for M in tau:
            tauM_to_vtx = [arrow[1] for arrow in self.arrows
                           if arrow[0] == tau[M]]
            # the list of vertices N s.t. there's arrow tauM -> N
            # (Multiple arrows are counted)
            from_M_vtx = [arrow[0] for arrow in self.arrows
                          if arrow[1] == M]
            # the list of vertices N s.t. there's arrow N -> M
            if Counter(tauM_to_vtx) != Counter(from_M_vtx):
                raise ValueError(f"{M} and its tau {tau[M]}"
                                 " doesn't satisfy the axiom!")

    def tau_plus(self, data: NQ) -> NQ:
        """Return the sum of tau (zero if not defined).

        We use a list of vertices, to represent an element
        of the free abelian monoid generated by vertices.
        Then this tau_plus is a monoid homomorphism.

        Args:
            data (NQ): An element of the free abelian monoid
                generated by vertices.

        Raises:
            ValueError: If some element in `data` is not in `self.vertex'.

        Returns:
            NQ: The sum of tau (represented by a list).
        """
        result: NQ = []
        for M in data:
            if M not in self.vertices:
                raise ValueError(f"{M} is not a vertex!")
            if M in self.tau:
                result.append(self.tau[M])
        try:
            return sorted(result)  # type: ignore
        except TypeError:
            return result

    def tau_minus(self, data: NQ) -> NQ:
        """Return the sum of tau^{-1} (zero if not defined).

        We use a list of vertices, to represent an element
        of the free abelian monoid generated by vertices.
        Then this tau_plus is a monoid homomorphism.

        Args:
            data (NQ): An element of the free abelian monoid
                generated by vertices.

        Raises:
            ValueError: If some element in `data` is not in `self.vertex'.

        Returns:
            NQ: The sum of tau^{-1} (represented by a list).
        """
        result: NQ = []
        for M in data:
            if M not in self.vertices:
                raise ValueError(f"{M} is not a vertex!")
            if M in self.tau_inv:
                result.append(self.tau_inv[M])
        try:
            return sorted(result)  # type: ignore
        except TypeError:
            return result

    def theta_plus(self, data: NQ) -> NQ:
        """Return the sum of theta.

        Theta of a vertex M is the sum of X s.t. there's an arrow X -> M.
        We use a list of vertices, to represent an element
        of the free abelian monoid generated by vertices.

        Args:
            data (NQ): An element of the free abelian monoid
                generated by vertices.

        Raises:
            ValueError: If some element in `data` is not in `self.vertex'.

        Returns:
            NQ: The sum of theta (represented by a list).
        """
        result: NQ = []
        for M in data:
            if M not in self.vertices:
                raise ValueError(f"{M} is not a vertex!")
            result.extend([ar[0] for ar in self.arrows if ar[1] == M])
        try:
            return sorted(result)  # type: ignore
        except TypeError:
            return result

    def theta_minus(self, data: NQ) -> NQ:
        """Return the sum of theta^{-}.

        Theta^{-} of a vertex M is the sum of X s.t. there's an arrow M -> X.
        We use a list of vertices, to represent an element
        of the free abelian monoid generated by vertices.

        Args:
            data (NQ): An element of the free abelian monoid
                generated by vertices.

        Raises:
            ValueError: If some element in `data` is not in `self.vertex'.

        Returns:
            NQ: The sum of theta^{-} (represented by a list).
        """
        result: NQ = []
        for M in data:
            if M not in self.vertices:
                raise ValueError(f"{M} is not a vertex!")
            result.extend([ar[1] for ar in self.arrows if ar[0] == M])
        try:
            return sorted(result)  # type: ignore
        except TypeError:
            return result

    def next_ladder_right(self, data: tuple[NQ, NQ]):
        """Go the next step of the right ladder.

        We have A -> B.
        This compute the next step: A' -> B' s.t.
        A'----> A
        |       |
        V       V
        B'----->B
        is the right ladder square.
        A' -> B' is obtained by:
        tau(B) -> (theta(B) - A)+.

        Args:
            data (tuple[NQ, NQ]): A -> B.

        Returns:
            tuple (A', B').
        """
        A, B = data
        return (self.tau_plus(B),
                substract(self.theta_plus(B), A))

    def next_ladder_left(self, data: tuple[NQ, NQ]):
        """Go the next step of the right ladder.

        We have A -> B.
        This compute the next step: A' -> B' s.t.
        A ----> A'
        |       |
        V       V
        B ----> B'
        is the left ladder square.
        A'->B' is obtained by:
        (theta_minus(A) - B)+ -> tau_minus(A).
        """
        A, B = data
        return (substract(self.theta_minus(A), B),
                self.tau_minus(A))

    def right_ladder_iter(self, map: tuple[NQ, NQ]):
        """An iterator of computing right ladder of (A -> B).
        This may be an infinite iterator if our category is not Hom-finite!

        Args:
            map (tuple[NQ, NQ]): A tuple (A, B),
                which we regard as a map A -> B

        Yields:
            tuple[NQ, NQ]: Yield 0-th term, 1st term, 2nd term, ...
                of the right ladder of (A -> B)
        """
        A, B = map
        current = (A, B)
        while True:
            yield current
            next = self.next_ladder_right(current)
            if next == ([], []):
                break
            current = next

    def left_ladder_iter(self, map: tuple[NQ, NQ]):
        """An iterator of computing left ladder of (A -> B).
        This may be an infinite iterator if our category is not Hom-finite!

        Args:
            map (tuple[NQ, NQ]): A tuple (A, B),
                which we regard as a map A -> B

        Yields:
            tuple[NQ, NQ]: Yield 0-th term, 1st term, 2nd term, ...
                of the left ladder of (A -> B)
        """
        A, B = map
        current = (A, B)
        while True:
            yield current
            next = self.next_ladder_left(current)
            if next == ([], []):
                break
            current = next

    def right_ladder(self,
                     map: tuple[NQ, NQ],
                     max: int = 1000) -> list[tuple[NQ, NQ]]:
        """Return the right ladder of map : A -> B.

        Args:
            vertex (Q): A vertex which should be in `self.vertices`.
            max (int): The maximum number of computation steps.

        Returns:
            If the computation successfully terminates, then it returns
            [(A, B), (A1, B1), ..., (An, Bn)],
            where the next of (An, Bn) is ([], []).
            If the computation is an infinite loop, then e.g.
            [(A0, B0), (A1, B1), ..., (A0, B0), (..., ...)],
            where the last two "..." are Ellipsis.
            If the computation doesn't stop after `max` steps, then
            [(A0, B0), ..., (A_max, B_max), (..., ...)],
            where the last two "..." are Ellipsis.
        """
        ladder: list[tuple[NQ, NQ]] = []
        ladder_iter = self.right_ladder_iter(map)
        i = 0
        for term in ladder_iter:
            if term == ([], []):
                break
            elif term in ladder or i == max:
                # Then this is an infinite loop or doesn't terminate.
                ladder.extend([term, (..., ...)])  # type: ignore
                break
            else:
                ladder.append(term)
                i = i + 1
        return ladder

    def left_ladder(self,
                    map: tuple[NQ, NQ],
                    max: int = 1000) -> list[tuple[NQ, NQ]]:
        """Return the right ladder of (0 -> vertex).

        Args:
            vertex (Q): A vertex which should be in `self.vertices`.
            max (int): The maximum number of computation steps.

        Returns:
            If the computation successfully terminates, then it returns
            [(A0, B0), (A1, B1), ..., (An, Bn)],
            where the next of (An, Bn) is ([], []).
            If the computation falls into an infinite loop, then e.g.
            [(A0, B0), (A1, B1), ..., (A0, B0), (..., ...)],
            where the last two "..." are Ellipsis.
            If the computation doesn't stop after `max` steps, then
            [(A0, B0), ..., (A_max, B_max), (..., ...)],
            where the last two "..." are Ellipsis.
        """
        ladder: list[tuple[NQ, NQ]] = []
        ladder_iter = self.left_ladder_iter(map)
        i = 0
        for term in ladder_iter:
            if term == ([], []):
                break
            elif term in ladder or i == max:
                # Then this is an infinite loop or doesn't terminate.
                ladder.extend([term, (..., ...)])  # type: ignore
                break
            else:
                ladder.append(term)
                i = i + 1
        return ladder

    def radical_layer(self, vertex: Q,
                      contravariant: bool = True) -> list[NQ]:
        """Return the radical layer of a Hom functor.

        If contravariant is true, then this computes
        J^n(-, vertex)/J^{n+1}(-, vertex) for each n >= 0.
        Thus this gives a composition series of Hom(-, vertex).
        If contravariant is false, then Hom(vertex, -) is considered.

        Args:
            vertex (Q): A vertex of `self`.
            contravariant (bool, optional): Defaults to True.

        Returns:
            list[NQ]: Return [[0-th layer], [1-th layer], ...]
            This list ends with "..." if the computation doesn't terminate.
        """
        if contravariant:
            return [x[1] for x in self.right_ladder(([], [vertex])) if x[1]]
        else:
            return [x[0] for x in self.left_ladder(([vertex], [])) if x[0]]

    def hom(self, X: Q, Y: Q) -> int:
        """Returns the dimension of Hom(X,Y).

        Args:
            X : vertex (regarded as an indecomposable object in C)
            Y : vertex (regarded as an indecomposable object in C)

        Raises:
            ValueError:
                - If self.is_tau_category is false, or
                - If the category is probably not Hom-finite, or
                - If two results using Hom(X,-) and Hom(-,Y)
                  differ. This may happen if the inputted AR quiver
                  is not an AR quiver of some tau-category.

        Returns:
            int: Returns the dimension of Hom(X,Y) over a base field.
        """
        if not self.is_tau_category:
            raise ValueError("This isn't a tau-category, hence can't compute!")
        # First compute using radical layer of Hom(-,Y).
        dim: int = 0
        dim2: int = 0
        try:
            for layer in self.radical_layer(Y):
                dim = dim + layer.count(X)
            for layer in self.radical_layer(X, contravariant=False):
                dim2 = dim2 + layer.count(Y)
        except AttributeError:  # Ellipsis appears.
            raise ValueError("Your category is probably not Hom-finite!")

        if dim != dim2:
            raise ValueError("Something wrong! Results using "
                             "Hom(X,-) and Hom(-,Y) don't coincide."
                             "Your category may not be a tau-category.")
        return dim

    def is_hom_orthogonal(self, X: Q, Y: Q) -> bool:
        """Return whether Hom(X, Y) = 0 = Hom(Y, X)

        Args:
            X (V): vertex (regarded as an indecomposable object in C)
            Y (V): vertex (regarded as an indecomposable object in C)

        Returns:
            bool: True if Hom(X, Y) = 0 = Hom(Y, X), otherwise False.
        """
        return self.hom(X, Y) == 0 and self.hom(Y, X) == 0

    def is_brick(self, X: Q) -> bool:
        """Return whether X is a brick.
        A brick is an object X s.t. End(X) is a division ring.
        Since we assume that our base field is algebraically closed
        or End(X)/rad End(X) = k,
        X is a brick if and only if End(X) = k.

        Args:
            X (V): vertex (regarded as an indecomposable object in C)

        Returns:
            bool: True if End(X) = k, otherwise False.
        """
        return self.hom(X, X) == 1

    def bricks(self) -> NQ:
        """Return the list of bricks.

        Returns:
            NQ: The list of bricks.
        """
        return [X for X in self.vertices if self.is_brick(X)]

    def maximal_orthogonals(self,
                            is_ortho: Callable[[Q, Q], bool],
                            base_set=None,
                            **kwargs) -> list[NQ]:
        """Return the list of maximal "orthogonal" objects.
        This is a helper method, used for various orthogonality conditions.

        Args:
            is_ortho (Callable[[Q, Q], bool]):
                A function which defines a orthogonality relation.
                e.g. is_ortho(X, Y) == True if X and Y are "orthogonal".
            base_set (optional):
                A base set on which we consider maximal orthogonals.
                Defaults to None. In this case, we may regard
                the set objects which are "self-orthogonal" as a base set.
            **kwargs: A keyword argument passed to `is_ortho`.

        Returns:
            list[NQ]: The list of maximal orthogonal objects.
                Note that we don't check self-orthogonality condition.
                (This will be useful when e.g. computing semibricks)
        """
        if base_set is None:
            base_set = [v for v in self.vertices if is_ortho(v, v, **kwargs)]
        neighbor = {v: [w for w in base_set
                        if v != w and is_ortho(v, w, **kwargs)]
                    for v in base_set}
        return maximal_cliques(neighbor)

    def orthogonals(self,
                    is_ortho: Callable[[Q, Q], bool],
                    base_set=None,
                    **kwargs) -> list[NQ]:
        """Return the list of "orthogonal" objects.
        This is a helper method, used for various orthogonality conditions.

        Args:
            is_ortho (Callable[[Q, Q], bool]):
                A function which defines a orthogonality relation.
                e.g. is_ortho(X, Y) == True if X and Y are "orthogonal".
            base_set (optional):
                A base set on which we consider maximal orthogonals.
                Defaults to None. In this case, we may regard
                the set objects which are "self-orthogonal" as a base set.
            **kwargs: A keyword argument passed to `is_ortho`.

        Returns:
            list[NQ]: The list of orthogonal objects.
                Note that we don't check self-orthogonality condition.
                (This will be useful when e.g. computing semibricks)
        """
        if base_set is None:
            base_set = [v for v in self.vertices if is_ortho(v, v, **kwargs)]
        neighbor = {v: [w for w in base_set
                        if v != w and is_ortho(v, w, **kwargs)]
                    for v in base_set}
        return cliques(neighbor)

    def maximal_semibricks(self) -> list[NQ]:
        """Return the list of maximal semibricks.
        A semibrick is a set of pair-wise Hom-orthogonal bricks.
        A semibrick is maximal if it is maximal w.r.t. direct sum.
        We only consider basic objects, that is,
        indecomposable summands are pairwise distinct.

        Returns:
            list[NQ]: The list of maximal semibricks.
                Each semibrick is represented by a list of vertices.
        """
        return self.maximal_orthogonals(self.is_hom_orthogonal, self.bricks())

    def semibricks(self) -> list[NQ]:
        """Return the list of all semibricks.
        A semibrick is a set of pair-wise Hom-orthogonal bricks.
        We only consider basic objects, that is,
        indecomposable summands are pairwise distinct.

        Returns:
            list[NQ]: The list of semibricks.
                Each semibrick is represented by a list of vertices.
        """
        return self.orthogonals(self.is_hom_orthogonal, self.bricks())

    # --- Methods related to triangulated categories ---
    #
    # If our category C is triangulated, then C satisfies
    # both (Case 1) tau-cat and (Case 2) extriangulated.

    def is_stable(self) -> bool:
        """Return whether `self` is a stable translation quiver.
        A translation quiver is said to be stable
        if tau and tau^{-1} are defined everywhere.
        """
        return len(self.tau) == len(self.vertices)

    def _shift(self, X: Q) -> Q:
        """Hidden method to return the shift of an indecomposable object.
        We assume that our category C is a Hom-finite triangulated category.
        In particular, `self` should be a stable translation quiver.

        Args:
            X (Q): vertex (regarded as an indecomposable object in C).

        Raises:
            ValueError: If computation fails.

        Returns:
            Q: Sigma(X), where Sigma is a shift functor.
        """
        # By the AR duality, we have
        # Hom(-, X[1]) = Ext^1(-,X) = D Hom(tau^{-1}X, -)
        # Thus X[1] is the socle of Hom(tau^{-1}X, -).

        layer = self.radical_layer(self.tau_inv[X], contravariant=False)
        if len(layer[-1]) != 1:
            raise ValueError("Something Wrong! Maybe not triangulated cat!")
        return layer[-1][0]

    def _shift_neg(self, X: Q) -> Q:
        """Hidden method to return the negative shift of an indecomposable object.
        We assume that our category C is a Hom-finite triangulated category.
        In particular, `self` should be a stable translation quiver.

        Args:
            X (Q): vertex (regarded as an indecomposable object in C).

        Raises:
            ValueError: If computation fails.

        Returns:
            Q: Sigma^{-1}(X), where Sigma is a shift functor.
        """
        # By the AR duality, we have
        # Hom(X[-1], -) = Hom(X, -[1]) = Ext^1(X, -) = D Hom(-, tauX)
        # Thus X[-1] is the socle of Hom(-, tauX).
        layer = self.radical_layer(self.tau[X])
        if len(layer[-1]) != 1:
            raise ValueError("Something Wrong! Maybe not triangulated cat!")
        return layer[-1][0]

    def shift(self, X: Q, n: int = 1) -> Q:
        """Return n-th shift of X.
        We assume that our category C is a Hom-finite triangulated category.

        Args:
            X (Q): Vertex (regarded as an indecomposable object in C).
            n (int, optional): Degree of shift. Defaults to 1.

        Raises:
            ValueError: If X is not in self.vertices.
            ValueError: If self is not a stable translation quiver.

        Returns:
            Q: Sigma^n(X), where Sigma is a shift functor.
        """
        if X not in self.vertices:
            raise ValueError(f"{X} is not a vertex!")
        if not self.is_stable():
            raise ValueError("Your translation quiver should be stable!")
        # Use recursion (induction) on n.
        result = X
        if n == 0:
            return X
        elif n > 0:
            for _ in range(n):
                result = self._shift(result)
            return result
        elif n < 0:
            for _ in range(-n):
                result = self._shift_neg(result)
            return result

    def Serre_functor(self, X: Q) -> Q:
        """Return the Serre functor of X.
        We assume that our category C is a Hom-finite triangulated category.
        Then Serre functor is a functor S s.t
        Hom(X,Y) is naturally isomorphic to D Hom(Y, SX),
        where D is the k-dual.
        It's well-known that S is the composition of tau and shift.

        Args:
            X (Q): Vertex (regarded as an indecomposable object in C).

        Raises:
            ValueError: If X is not in `self.vertices`.

        Returns:
            Q: S(X) (= Sigma(tau(X)) ), where S is the Serre functor.
        """
        if X not in self.vertices:
            raise ValueError(f"{X} is not a vertex!")
        return self.shift(self.tau[X])

    def is_ext_orthogonal(self, X: Q, Y: Q, degrees: list[int] = [1]) -> bool:
        """Return whether X and Y are orthogonal w.r.t. the designated degree.
        Ext^n(X,Y) is defined to be Hom(X, Y[n]) for triangulated categories.
        This returns true if Ext^n(X,Y) and Ext^n(Y,X) vanish
        for every n in `degrees`.

        Args:
            X (Q): Vertex (regarded as an indecomposable object in C).
            Y (Q): Vertex (regarded as an indecomposable object in C).
            degrees (list[int], optional):
                The list of degrees n s.t. we want Ext^n = 0.
                Defaults to [1], hence we check Ext^1 = 0.
        """
        for n in degrees:
            if self.hom(X, self.shift(Y, n)) != 0:
                return False
            elif self.hom(Y, self.shift(X, n)) != 0:
                return False
        return True

    def maximal_ext_orthogonals(self, degrees: list[int] = [1]) -> list[NQ]:
        """Return the list of maximal "self-orthogonal" objects.
        For an object M in our category, we say it's self-orthogonal
        if Ext^n(M, M) := Hom(M, M[n]) = 0 for every n in `degrees`.

        Args:
            degrees (list[int], optional):
                The list of integers "n" s.t. we want Ext^n to vanish.
                Defaults to [1], namely, it returns maximal Ext^1 orthogonals.
        """
        return self.maximal_orthogonals(self.is_ext_orthogonal,
                                        degrees=degrees)

    def ext_orthogonals(self, degrees: list[int] = [1]) -> list[NQ]:
        """Return the list of "self-orthogonal" objects.
        For an object M in our category, we say it's self-orthogonal
        if Ext^n(M, M) := Hom(M, M[n]) = 0 for every n in `degrees`.
        NOTE: 0 object (= []) is considered as self-orthogonal.

        Args:
            degrees (list[int], optional):
                The list of integers "n" s.t. we want Ext^n to vanish.
                Defaults to [1], namely, it returns maximal Ext^1 orthogonals.
        """
        return self.orthogonals(self.is_ext_orthogonal, degrees=degrees)

    def period(self) -> int:
        """Return the period of shift functor ON OBJECTS.
        This compute the smallest n > 0 s.t.
        Sigma^n(X) is isomorphic to X for every X.
        This DOES NOT consider an action of Sigma on Hom,
        hence this period may be different from the period of shift functor,
        which is defined by the smallest n
        s.t. Sigma^n and id are naturally isomorphic.
        """
        obj_periods: list[int] = []
        for X in self.vertices:
            working = X
            i = 1
            while True:
                working = self._shift(working)
                if working == X:
                    break
                i = i + 1
            obj_periods.append(i)
        return lcm(*obj_periods)
