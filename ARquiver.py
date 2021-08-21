"""A module for a class for finite translation quiver.

In this module, we define a class `TranslationQuiver`,
which is a class for finite translation quiver.
For a TranslationQuiver object, there are some methods
to compute various things.
We often identify a translation quiver and a certain kind of additive category,
see the docstring of `TranslationQuiver`.

So far, the computation of the dimension of Hom(X,Y)
and the composition series of Hom functors are implemented.

In the near(?) future, the various methods will be available.


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
from collections.abc import Hashable
from functools import cache
from typing import Counter

V = Hashable  # Type for vertices


def substract(lst1: list[V], lst2: list[V]) -> list[V]:
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


class TranslationQuiver():
    """A class of finite translation quivers.

    We assume that the inputted quiver is the AR quiver of
    either of the following classes of categories:
    (CASE 1) tau-categories.
    (CASE 2) Extriangulated categories with AR conflations.
    When you create a TranslationQuiver object,
    we ask that which case your category is (default: CASE 1).
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
    (CASE 1) C is a tau-category.
    (CASE 2) C is an extriangulated category with AR conflations.
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

    --- Difference between (CASE 1) and (CASE 2) ---
    For (CASE 1), the AR quiver of a tau-category well describes the additive
    structure of the original category.
    For example, one can calculate the dimension of Hom, or more strongly,
    one can compute the radical series of Hom functors.

    For (Case 2), one cannot except such a calculation,
    since the additive structure cannot be approximated by the AR quiver.
    However, by taking the stable category, one may still compute
    Ext^1, stable Hom, and so on.

    Thus some methods below are only allowed for (CASE 1).
    """

    def __init__(self,
                 vertices: tuple[V, ...],
                 arrows: tuple[tuple[V, V], ...],
                 tau: dict[V, V],
                 is_tau_category: bool = True) -> None:
        """Construct

        Args:
            vertices: The tuple of vertices.
                Each vertex should be hashable, e.g. shouldn't be a list,
                because we use Counter() for list of vertices.
            arrows: The tuple of arrows.
                each arrow is a tuple of the form (`source`, `target`)
                with `source`, `target` in `vertices`.
            tau: A dictionary of AR translation.
            is_tau_category: Whether the considered category is a tau-category
                (CASE 1). Default: True.

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

    def tau_plus(self, data: list[V]) -> list[V]:
        """Return the sum of tau (zero if not defined).

        We use a list of vertices, to represent an element
        of the free abelian monoid generated by vertices.
        Then this tau_plus is a monoid homomorphism.

        Args:
            data (list[V]): An element of the free abelian monoid
                generated by vertices.

        Raises:
            ValueError: If some element in `data` is not in `self.vertex'.

        Returns:
            list[V]: The sum of tau (represented by a list).
        """
        result: list[V] = []
        for M in data:
            if M not in self.vertices:
                raise ValueError(f"{M} is not a vertex!")
            if M in self.tau:
                result.append(self.tau[M])
        try:
            return sorted(result)  # type: ignore
        except TypeError:
            return result

    def tau_minus(self, data: list[V]) -> list[V]:
        """Return the sum of tau^{-1} (zero if not defined).

        We use a list of vertices, to represent an element
        of the free abelian monoid generated by vertices.
        Then this tau_plus is a monoid homomorphism.

        Args:
            data (list[V]): An element of the free abelian monoid
                generated by vertices.

        Raises:
            ValueError: If some element in `data` is not in `self.vertex'.

        Returns:
            list[V]: The sum of tau^{-1} (represented by a list).
        """
        result: list[V] = []
        for M in data:
            if M not in self.vertices:
                raise ValueError(f"{M} is not a vertex!")
            if M in self.tau_inv:
                result.append(self.tau_inv[M])
        try:
            return sorted(result)  # type: ignore
        except TypeError:
            return result

    def theta_plus(self, data: list[V]) -> list[V]:
        """Return the sum of theta.

        Theta of a vertex M is the sum of X s.t. there's an arrow X -> M.
        We use a list of vertices, to represent an element
        of the free abelian monoid generated by vertices.

        Args:
            data (list[V]): An element of the free abelian monoid
                generated by vertices.

        Raises:
            ValueError: If some element in `data` is not in `self.vertex'.

        Returns:
            list[V]: The sum of theta (represented by a list).
        """
        result: list[V] = []
        for M in data:
            if M not in self.vertices:
                raise ValueError(f"{M} is not a vertex!")
            result.extend([ar[0] for ar in self.arrows if ar[1] == M])
        try:
            return sorted(result)  # type: ignore
        except TypeError:
            return result

    def theta_minus(self, data: list[V]) -> list[V]:
        """Return the sum of theta^{-}.

        Theta^{-} of a vertex M is the sum of X s.t. there's an arrow M -> X.
        We use a list of vertices, to represent an element
        of the free abelian monoid generated by vertices.

        Args:
            data (list[V]): An element of the free abelian monoid
                generated by vertices.

        Raises:
            ValueError: If some element in `data` is not in `self.vertex'.

        Returns:
            list[V]: The sum of theta^{-} (represented by a list).
        """
        result: list[V] = []
        for M in data:
            if M not in self.vertices:
                raise ValueError(f"{M} is not a vertex!")
            result.extend([ar[1] for ar in self.arrows if ar[0] == M])
        try:
            return sorted(result)  # type: ignore
        except TypeError:
            return result

    def next_ladder_right(self, data: tuple[list[V], list[V]]):
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
            data (tuple[list[V], list[V]]): A -> B.

        Returns:
            tuple (A', B').
        """
        A, B = data
        return (self.tau_plus(B),
                substract(self.theta_plus(B), A))

    def next_ladder_left(self, data: tuple[list[V], list[V]]):
        A, B = data
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
        return (substract(self.theta_minus(A), B),
                self.tau_minus(A))

    @cache
    def right_partial_ladder(self,
                             vertex: V,
                             n: int) -> tuple[list[V], list[V]]:
        """Return the n-th term of the right ladder of (0 -> vertex).
        This is tau(theta_{n-1}) (vertex) -> theta_n (vertex)
        in Iyama's notation.
        Then (-,A_n) -> (-,B_n) -> J^n(-,vertex) -> 0 is
        a minimal projective presentation.
        See e.g. [Iy1], [Iy3], [INP] for the definition of ladders.

        Args:
            vertex (V): A vertex which should be in `self.vertices`
            n (int): A non-negative integer.

        Raises:
            ValueError: If n < 0.

        Returns:
            tuple[list[V], list[V]]: tuple (A_n, B_n).
        """
        # We use recurrence.
        if n < 0:
            raise ValueError("n must be non-negative.")
        if n == 0:
            A0: list[V] = []
            return (A0, [vertex])
        else:
            previous = self.right_partial_ladder(vertex, n-1)
            return self.next_ladder_right(previous)

    @cache
    def left_partial_ladder(self,
                            vertex: V,
                            n: int) -> tuple[list[V], list[V]]:
        """Return the n-th term of the left ladder of (vertex -> 0).
        If its n-th term is (A_n -> B_n), then
        Then (B_n,-) -> (A_n,-) -> J^n(vertex, -) -> 0 is
        a minimal projective presentation.
        See e.g. [Iy1], [Iy3], [INP] for the definition of ladders.

        Args:
            vertex (V): A vertex which should be in `self.vertices`
            n (int): A non-negative integer.

        Raises:
            ValueError: If n < 0.

        Returns:
            tuple[list[V], list[V]]: tuple (A_n, B_n).
        """
        # We use recurrence.
        if n < 0:
            raise ValueError("n must be non-negative.")
        if n == 0:
            B0: list[V] = []
            return ([vertex], B0)
        else:
            previous = self.left_partial_ladder(vertex, n-1)
            return self.next_ladder_left(previous)

    def right_ladder(self, vertex: V) -> list[tuple[list[V], list[V]]]:
        """Return the right ladder of (0 -> vertex).

        Args:
            vertex (V): A vertex which should be in `self.vertices`.

        Raises:
            ValueError: If the computation goes into an infinite loop.
            Warning: If the computation doesn't terminate after 1000 steps.

        Returns:
            list[tuple[list[V], list[V]]]: [(A0, B0), (A1, B1), ...]
        """
        ladder: list[tuple[list[V], list[V]]] = []
        for i in range(1001):  # i = 0, 1, ..., 1000
            ith_ladder = self.right_partial_ladder(vertex, i)
            if ith_ladder in ladder:
                raise ValueError("Ladder is infinite!")
            if ith_ladder == ([], []):
                break
            ladder.append(ith_ladder)
        if i == 1000:
            raise Warning("The computation doesn't terminate after 1000 steps,"
                          " hence this category may not be artinian.")
        return ladder

    def left_ladder(self, vertex: V) -> list[tuple[list[V], list[V]]]:
        """Return the left ladder of (vertex -> 0).

        Args:
            vertex (V): A vertex which should be in `self.vertices`.

        Raises:
            ValueError: If the computation goes into an infinite loop.
            Warning: If the computation doesn't terminate after 1000 steps.

        Returns:
            list[tuple[list[V], list[V]]]: [(A0, B0), (A1, B1), ...]
        """
        ladder: list[tuple[list[V], list[V]]] = []
        for i in range(1001):  # i = 0, 1, ..., 1000
            ith_ladder = self.left_partial_ladder(vertex, i)
            if ith_ladder in ladder:
                raise ValueError("Ladder is infinite!")
            if ith_ladder == ([], []):
                break
            ladder.append(ith_ladder)
        if i == 1000:
            raise Warning("The computation doesn't terminate after 1000 steps,"
                          " hence this category may not be artinian.")
        return ladder

    def radical_layer(self, vertex: V,
                      contravariant: bool = True) -> list[list[V]]:
        """Return the radical layer of a Hom functor.

        If contravariant is true, then this computes
        J^n(-, vertex)/J^{n+1}(-, vertex) for each n >= 0.
        Thus this gives a composition series of Hom(-, vertex).
        If contravariant is false, then Hom(vertex, -) is considered.

        Args:
            vertex (V): A vertex of `self`.
            contravariant (bool, optional): Defaults to True.

        Returns:
            list[list[V]]: Return [[0-th layer], [1-th layer], ...]
        """
        if contravariant:
            return [x[1] for x in self.right_ladder(vertex)]
        else:
            return [x[0] for x in self.left_ladder(vertex)]

    def hom(self, X: V, Y: V) -> int:
        """Returns the dimension of Hom(X,Y).

        Args:
            X : vertex
            Y : vertex

        Raises:
            ValueError:
                If self.is_tau_category is false, or
                if two results using Hom(X,-) and Hom(-,Y)
                differ. This may happen if the inputted AR quiver
                is not an AR quiver of some tau-category.

        Returns:
            int: Returns the dimension of Hom(X,Y) over a base field.
        """
        if not self.is_tau_category:
            raise ValueError("This isn't a tau-category, hence can't compute!")
        # First compute using radical layer of Hom(-,Y).
        dim: int = 0
        for layer in self.radical_layer(Y):
            dim = dim + layer.count(X)

        # Next we compute using Hom(X,-).
        dim2: int = 0
        for layer in self.radical_layer(X, contravariant=False):
            dim2 = dim2 + layer.count(Y)

        if dim != dim2:
            raise ValueError("Something wrong! Results using "
                             "Hom(X,-) and Hom(-,Y) don't coincide."
                             "Your category may not be a tau-category.")
        return dim
