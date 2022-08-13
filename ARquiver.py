"""A module for a class for finite translation quiver.

In this module, we define a class `TranslationQuiver`,
which is a class for finite translation quiver.
For a TranslationQuiver object, there are some methods
to compute various things.
We identify a translation quiver and a certain kind of additive category,
see the docstring of `TranslationQuiver`.

References:

    [AP] S.Asai, C. Pfeifer, Wide subcategories and lattices of torsion classes,
        arXiv:1905.01148.

    [En] H. Enomoto, From the lattice of torsion classes to the posets
        of wide subcategories and ICE-closed subcategories, arXiv:2201.00595.

    [ES] H. Enomoto, A. Sakai,
        ICE-closed subcategories and wide $\tau$-tilting modules,
        Math. Z. 300 (2022), no. 1, 541--577.

    [Iy1] O. Iyama, tau-categories I: Ladders,
        Algebr. Represent. Theory 8 (2005), no. 3, 297--321.

    [Iy2] O. Iyama, tau-categories II:
        Nakayama pairs and Rejective subcategories,
        Algebr. Represent. Theory 8 (2005), no. 4, 449--477.

    [Iy3] O. Iyama, The relationship between homological properties
        and representation theoretic realization of artin algebras,
        Trans. Amer. Math. Soc. 357 (2005), no. 2, 709--734.

    [INP] O. Iyama, H. Nakaoka, Y. Palu,
        Auslander-Reiten theory in extriangulated categories, arXiv:1805.03776.
"""

from __future__ import annotations
from collections.abc import Hashable, Callable, Collection
from dataclasses import dataclass, field
from functools import cache
import itertools
from math import lcm
from typing import Counter, Generic, TypeVar, Optional

T = TypeVar("T", bound=Hashable)


def substract(lst1: list[T], lst2: list[T]) -> list[T]:
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


def maximal_cliques(neighbor: dict[T, list[T]]) -> list[frozenset[T]]:
    """Search maximal cliques in a graph using Bron-Kerbosch algorithm.
    Will be used to search maximal orthogonal objects,
    e.g. tau-tilting, n-cluster-tilting, etc.,

    Args:
        neighbor: Dictionary of neighbor.
            We assume this is simple graph, namely, v not in neighbor[v].

    Returns:
        The list of all maximal cliques.
    """
    all_vertices = set(neighbor.keys())

    def BronKerbosch(clique: set[T], candidates: set[T], excluded: set[T]):
        if not candidates and not excluded:
            yield clique
        elif not candidates:
            return
        else:
            # Choose one pivot from `candidates`, which is non-empty now.
            for pivot in candidates:
                break
            assert pivot  # type: ignore
            search = {x for x in candidates if x not in neighbor[pivot]}
            # search = candidates[:]
            for v in search:
                new_candidates = {x for x in candidates if x in neighbor[v]}
                new_excluded = {x for x in excluded if x in neighbor[v]}
                yield from BronKerbosch(clique | {v},
                                        new_candidates,
                                        new_excluded)
                candidates.remove(v)
                excluded.add(v)
    result = list(BronKerbosch(set(), all_vertices, set()))
    return [frozenset(val) for val in result]


def cliques(neighbor: dict[T, list[T]]) -> list[frozenset[T]]:
    """Search all cliques in a graph using (variant of) Bron-Kerbosch algorithm.
    Will be used to search self-orthogonal objects,
    e.g. semibricks, rigid modules, etc.

    Args:
        neighbor: Dictionary of neighbor.
            We assume this is simple graph, namely, v not in neighbor[v].

    Returns:
        The list of all maximal cliques.
    """
    all_vertices = set(neighbor.keys())

    def BK_modified(clique: set[T], candidates: set[T], excluded: set[T]):
        # print(f"{clique}, {candidates}, {excluded}")
        yield clique
        if not candidates:
            return
        else:
            search = candidates.copy()
            for v in search:
                new_candidates = {x for x in candidates if x in neighbor[v]}
                new_excluded = {x for x in excluded if x in neighbor[v]}
                yield from BK_modified(clique | {v},
                                       new_candidates,
                                       new_excluded)
                candidates.remove(v)
                excluded.add(v)
    result = list(BK_modified(set(), all_vertices, set()))
    return [frozenset(val) for val in result]


@dataclass
class TranslationQuiver(Generic[T]):
    """A (data)class of finite translation quivers.

    Args:
        vertices: A set (any Iterable) of vertices in the quiver.
            Each vertex should be hashable, e.g. shouldn't be a list.
        arrows: A set (any Iterable) of arrows.
            each arrow is a tuple of the form (`source`, `target`)
            with `source`, `target` in `vertices`.
        tau: A dictionary of AR translation.
        tau_inv: A dictionary of tau^{-1}.
        is_tau_category:
            Whether the considered category is a tau-category.
            Default: True.
        is_ET_category:
            Whether our quiver is the AR quiver of an extriangulated categories.
            Default: True.

    --- Details ---

    We assume that the inputted quiver is the AR quiver of
    either of the following classes of categories:
    (Case 1) tau-categories.
    (Case 2) Extriangulated categories with AR conflations.
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
    T: For vertices.
    list[T]: For formal sum of vertices, or more precisely,
        elements of the free abelian monoid generated by vertices.
        For example, [X, X] represents X + X,
        [X, X, Y, Z] represents 2X + Y + Z.
        It's also used to represent an object in our category.
        For example, [X, X, Y, Z] represents X^2 oplus Y oplus Z.
    Collection[T]: For objects in our category which is not necessarily basic.
        This includes list[T], tuple[T], set[T], frozenset[T], etc.
    Hashable[T]: Same as Collection[T], but used to enable @cache.
    frozenset[T]: For subcategories (closed under direct sum and summands),
        and also for basic objects.
        The reason we use frozenset is that this is hashable and we can
        consider the set of frozensets.
        For example, frozenset({X, Y, Z}) represents the additive closure
        of X, Y, and Z, or an basic object X oplus Y oplus Z.
    """
    vertices: Collection[T]
    arrows: Collection[tuple[T, T]]
    tau: dict[T, T]
    tau_inv: dict[T, T] = field(init=False)
    # Automatically generated in self.__post_init__().
    is_tau_category: bool = True
    is_ET_category: bool = False

    def __post_init__(self) -> None:
        """
        Check whether the inputted data satisfies the axiom of translation quivers.
        Also makes self.tau_inv.

        Raises:
            ValueError: If it doesn't satisfy the axiom of
                the translation quiver.
        """
        self.tau_inv = {v: k for k, v in self.tau.items()}
        # the dictionary of tau^{-1}

        # Check whether the constructed data is actually a translation quiver.
        # First check that tau is a partial injection
        if len(self.tau) != len(self.tau_inv):
            raise ValueError("tau is not injective")
        # Next check whether it satisfies the axiom of translation quiver
        for M in self.tau:
            tauM_to_vtx = [arrow[1] for arrow in self.arrows
                           if arrow[0] == self.tau[M]]
            # the list of vertices N s.t. there's arrow tauM -> N
            # (Multiple arrows are counted)
            from_M_vtx = [arrow[0] for arrow in self.arrows
                          if arrow[1] == M]
            # the list of vertices N s.t. there's arrow N -> M
            if Counter(tauM_to_vtx) != Counter(from_M_vtx):
                raise ValueError(f"{M} and its tau {self.tau[M]}"
                                 " doesn't satisfy the axiom!")

    # We make our instance hashable to use @cache decorator.
    def __hash__(self):
        return hash((frozenset(self.vertices), frozenset(self.arrows),
                     frozenset(self.tau.items())))

    # --- Methods to make new `TranslationQuiver` objects ---
    def ideal_quotient(self, subcat: Collection[T]) -> TranslationQuiver[T]:
        """Construct a new translation quiver corresponding
        to the ideal quotient `C/[subcat]` by a subcategory `subcat`.
        More precisely, it returns a new translation quiver obtained by
        deleting all vertices in a given subcategory.
        Main use is to compute Hom in (projectively) stable category.

        In (Case 1), this construction gives the AR quiver
        of the ideal quotient, which is actually also a tau-category.
        In (Case 2), the ideal quotient may not have a natural extriangulated
        structure. However, if we consider the projectively stable
        category, then it becomes a tau-category by [INP],
        and this construction gives the AR quiver of it.

        Args:
            subcat (frozenset[T]): A subcategory.
        """
        new_vertices = frozenset(self.vertices) - frozenset(subcat)
        new_arrows = [ar for ar in self.arrows
                      if ar[0] in new_vertices and ar[1] in new_vertices]
        new_tau: dict[T, T] = {}
        for vtx in self.tau.keys():
            if (vtx in subcat) or (self.tau[vtx] in subcat):
                continue
            to_vtx = [ar for ar in new_arrows if ar[1] == vtx]
            if to_vtx and self.tau[vtx] in new_vertices:
                new_tau[vtx] = self.tau[vtx]
        return TranslationQuiver(new_vertices, new_arrows, new_tau)

    def projectives(self) -> list[T]:
        """Return the list of all projective vertices.
        A vertex is projective if tau is not defined."""
        return [X for X in self.vertices if X not in self.tau]

    def injectives(self) -> list[T]:
        """Return the list of all injective vertices.
        A vertex is injective if tau^{-1} is not defined."""
        return [X for X in self.vertices if X not in self.tau_inv]

    def projectively_stable(self) -> TranslationQuiver[T]:
        """Return the translation quiver of the projectively stable category.
        The projectively stable category is the ideal quotient of our category
        by the subcategory of all projective objects.

        This works if our category is extriangulated with enough projectives,
        and in this case the resulting category is a tau-category by [INP].
        """
        return self.ideal_quotient(frozenset(self.projectives()))

    def injectively_stable(self) -> TranslationQuiver[T]:
        """Return the translation quiver of the injectively stable category.
        The injectively stable category is the ideal quotient of our category
        by the subcategory of all injective objects.

        This works if our category is extriangulated with enough injectives.
        and in this case the resulting category is a tau-category by [INP].
        """
        return self.ideal_quotient(frozenset(self.injectives()))

    # --- Methods used to compute ladders and Hom ---

    def tau_plus(self, data: list[T]) -> list[T]:
        """Return the sum of tau (zero if not defined).

        We use a list of vertices, to represent an element
        of the free abelian monoid generated by vertices.
        Then this tau_plus is a monoid homomorphism.

        Args:
            data: An element of the free abelian monoid
                generated by vertices.

        Raises:
            ValueError: If some element in `data` is not in `self.vertex'.

        Returns:
            The sum of tau (represented by a list).
        """
        result: list[T] = []
        for M in data:
            if M not in self.vertices:
                raise ValueError(f"{M} is not a vertex!")
            if M in self.tau:
                result.append(self.tau[M])
        return result

    def tau_minus(self, data: list[T]) -> list[T]:
        """Return the sum of tau^{-1} (zero if not defined).

        We use a list of vertices, to represent an element
        of the free abelian monoid generated by vertices.
        Then this tau_plus is a monoid homomorphism.

        Args:
            data: An element of the free abelian monoid
                generated by vertices.

        Raises:
            ValueError: If some element in `data` is not in `self.vertex'.

        Returns:
            The sum of tau^{-1} (represented by a list).
        """
        result: list[T] = []
        for M in data:
            if M not in self.vertices:
                raise ValueError(f"{M} is not a vertex!")
            if M in self.tau_inv:
                result.append(self.tau_inv[M])
        return result

    def theta_plus(self, data: list[T]) -> list[T]:
        """Return the sum of theta.

        Theta of a vertex M is the sum of X s.t. there's an arrow X -> M.
        We use a list of vertices, to represent an element
        of the free abelian monoid generated by vertices.

        Args:
            data: An element of the free abelian monoid
                generated by vertices.

        Raises:
            ValueError: If some element in `data` is not in `self.vertex'.

        Returns:
            The sum of theta (represented by a list).
        """
        result: list[T] = []
        for M in data:
            if M not in self.vertices:
                raise ValueError(f"{M} is not a vertex!")
            result.extend([ar[0] for ar in self.arrows if ar[1] == M])
        return result

    def theta_minus(self, data: list[T]) -> list[T]:
        """Return the sum of theta^{-}.

        Theta^{-} of a vertex M is the sum of X s.t. there's an arrow M -> X.
        We use a list of vertices, to represent an element
        of the free abelian monoid generated by vertices.

        Args:
            data: An element of the free abelian monoid
                generated by vertices.

        Raises:
            ValueError: If some element in `data` is not in `self.vertex'.

        Returns:
            The sum of theta^{-} (represented by a list).
        """
        result: list[T] = []
        for M in data:
            if M not in self.vertices:
                raise ValueError(f"{M} is not a vertex!")
            result.extend([ar[1] for ar in self.arrows if ar[0] == M])
        return result

    def next_ladder_right(self, data: tuple[list[T], list[T]]):
        """Go the next step of the right ladder.

        We have data = (A, B), represents a map A -> B.
        This compute the next step: A' -> B' s.t.
        A'----> A
        |       |
        V       V
        B'----->B
        is the right ladder square.
        A' -> B' is obtained by:
        tau(B) -> (theta(B) - A)+.

        Args:
            data: (A, B), representing a map A -> B.

        Returns:
            tuple (A', B').
        """
        A, B = data
        return (self.tau_plus(B),
                substract(self.theta_plus(B), A))

    def next_ladder_left(self, data: tuple[list[T], list[T]]):
        """Go the next step of the right ladder.

        We have data = (A, B), representing a map A -> B.
        This compute the next step: A' -> B' s.t.
        A ----> A'
        |       |
        V       V
        B ----> B'
        is the left ladder square.
        A'->B' is obtained by:
        (theta_minus(A) - B)+ -> tau_minus(A).

        Args:
            data: (A, B), representing a map A -> B.

        Returns:
            tuple (A', B').
        """
        A, B = data
        return (substract(self.theta_minus(A), B),
                self.tau_minus(A))

    def right_ladder_iter(self, map: tuple[list[T], list[T]]):
        """An iterator of computing right ladder of (A -> B).
        This may be an infinite iterator if our category is not Hom-finite!

        Args:
            map: A tuple (A, B), representing a map A -> B

        Yields:
            Yield 0-th term, 1st term, 2nd term, ...
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

    def left_ladder_iter(self, map: tuple[list[T], list[T]]):
        """An iterator of computing left ladder of (A -> B).
        This may be an infinite iterator if our category is not Hom-finite!

        Args:
            map: A tuple (A, B), representing a map A -> B

        Yields:
            Yield 0-th term, 1st term, 2nd term, ...
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
                     map: tuple[list[T], list[T]],
                     max: int = 1000) -> list[tuple[list[T], list[T]]]:
        """Return the right ladder of map : A -> B.

        Args:
            vertex: A vertex which should be in `self.vertices`.
            max: A maximum number of computation steps.

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
        ladder: list[tuple[list[T], list[T]]] = []
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
                    map: tuple[list[T], list[T]],
                    max: int = 1000) -> list[tuple[list[T], list[T]]]:
        """Return the right ladder of (0 -> vertex).

        Args:
            vertex: A vertex which should be in `self.vertices`.
            max: A maximum number of computation steps.

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
        ladder: list[tuple[list[T], list[T]]] = []
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

    def radical_layer(self, vertex: T,
                      contravariant: bool = True) -> list[list[T]]:
        """Return the radical layer of a Hom functor.

        If contravariant is true, then this computes
        J^n(-, vertex)/J^{n+1}(-, vertex) for each n >= 0.
        Thus this gives a composition series of Hom(-, vertex).
        If contravariant is false, then Hom(vertex, -) is considered.

        Args:
            vertex: A vertex of `self`.
            contravariant: A boolean. Defaults to True.

        Returns:
            list[list[T]]: Return [[0-th layer], [1-th layer], ...]
            This list ends with "..." if the computation doesn't terminate.
        """
        if contravariant:
            return [x[1] for x in self.right_ladder(([], [vertex])) if x[1]]
        else:
            return [x[0] for x in self.left_ladder(([vertex], [])) if x[0]]

    @cache
    def hom(self, X: T, Y: T) -> int:
        """Returns the dimension of Hom(X,Y) for two indecomposables.

        Args:
            X : vertex (regarded as an indecomposable object in C)
            Y : vertex (regarded as an indecomposable object in C)

        Raises:
            ValueError:
                - If self.is_tau_category is false, or
                - If the category is probably not Hom-finite, or
                - If two results using Hom(X,-) and Hom(-,Y)
                  differ.

        Returns:
            Returns the dimension of Hom(X,Y) over a base field.
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

    @cache
    def ext(self, X: T, Y: T) -> int:
        """
        Return dim_k Ext^1(X,Y) using generalized AR duality [INP]:
        D Ext(X, Y) = C_pst (tau^{-1} Y, X) = C_ist (Y, tau X)
        This works if our category is extriangulated (Case 2)
        and has enough projectives and injectives.
        """
        if X in self.projectives() or Y in self.injectives():
            return 0
        else:
            dim = self.projectively_stable().hom(self.tau_inv[Y], X)
            dim2 = self.injectively_stable().hom(Y, self.tau[X])
            if dim != dim2:
                raise ValueError("tau doesn't give equiv between "
                                 "projectively stable and injectively stable "
                                 "categories.")
            return dim

    def _hom(self, M: Collection[T], N: Collection[T]) -> int:
        """Return the dimension of Hom(M, N) for non-indec objects.
        """
        return sum(self.hom(X, Y) for X in M for Y in N)

    def is_hom_orthogonal(self, X: T, Y: T) -> bool:
        """Return whether Hom(X, Y) = 0 = Hom(Y, X) for two indecomposables.
        """
        return self.hom(X, Y) == 0 and self.hom(Y, X) == 0

    def is_hom_perp(self, M: Collection[T], N: Collection[T]) -> bool:
        """Return whether Hom(M, N) = 0 for possibly non-indec objects.
        """
        for X in M:
            for Y in N:
                if self.hom(X, Y) != 0:
                    return False
        return True

    @cache
    def hom_perp_right(self, M: Hashable[T]) -> frozenset[T]:
        r"""Return the subcategory consisting of Y s.t. Hom(M, Y) = 0.
        This is the Hom right perpendicular category $M^\perp$.
        Args:
            M: An object of C (possibly not indecomposable)

        Returns:
            The frozenset of indecomposables Y with Hom(M, Y) = 0.
        """
        return frozenset([Y for Y in self.vertices
                          if self.is_hom_perp(M, [Y])])

    @cache
    def hom_perp_left(self, M: Hashable[T]) -> frozenset[T]:
        r"""Return the subcategory consisting of X s.t. Hom(X, M) = 0.
        This is the Hom right perpendicular category $^\perp M$.
        Args:
            M: An object of C (possibly not indecomposable)

        Returns:
            The frozenset of indecomposables X with Hom(X, M) = 0.
        """
        return frozenset([X for X in self.vertices
                          if self.is_hom_perp([X], M)])

    def is_brick(self, X: T) -> bool:
        """Return whether an indecomposable X is a brick.
        A brick is an object X s.t. End(X) is a division ring.
        Since we assume that our base field is algebraically closed
        or End(X)/rad End(X) = k,
        X is a brick if and only if End(X) = k.
        """
        return self.hom(X, X) == 1

    def bricks(self) -> list[T]:
        """Return the list of bricks.
        """
        return [X for X in self.vertices if self.is_brick(X)]

    def maximal_orthogonals(self,
                            is_ortho: Callable[[T, T], bool],
                            base_set: Optional[Collection[T]] = None,
                            **kwargs) -> list[frozenset[T]]:
        """Return the list of maximal "orthogonal" objects.
        This is a helper method, used for various orthogonality conditions.

        Args:
            is_ortho:
                A function which defines a orthogonality relation.
                e.g. is_ortho(X, Y) == True if X and Y are "orthogonal".
            base_set (optional):
                A base set of indecomposables on which we consider maximal orthogonals.
                Defaults to None. In this case, we may regard
                the set indecomposable objects which are "self-orthogonal" as a base set.
            **kwargs: A keyword argument passed to `is_ortho`.

        Returns:
            list[set[T]]: The list of maximal orthogonal objects.
                Each object is represented by the set of vertices.
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
                    is_ortho: Callable[[T, T], bool],
                    base_set: Optional[Collection[T]] = None,
                    **kwargs) -> list[frozenset[T]]:
        """Return the list of "orthogonal" objects.
        This is a helper method, used for various orthogonality conditions.

        Args:
            is_ortho:
                A function which defines a orthogonality relation.
                e.g. is_ortho(X, Y) == True if X and Y are "orthogonal".
            base_set (optional):
                A base set of indecomposables on which we consider maximal orthogonals.
                Defaults to None. In this case, we may regard
                the set of indecomposable objects which are "self-orthogonal" as a base set.
            **kwargs: A keyword argument passed to `is_ortho`.

        Returns:
            list[set[T]]: The list of orthogonal objects.
                Each object is represented by the set of vertices.
                Note that we don't check self-orthogonality condition.
        """
        if base_set is None:
            base_set = [v for v in self.vertices if is_ortho(v, v, **kwargs)]
        neighbor = {v: [w for w in base_set
                        if v != w and is_ortho(v, w, **kwargs)]
                    for v in base_set}
        return cliques(neighbor)

    @cache
    def semibricks(self) -> list[frozenset[T]]:
        """Return the list of all semibricks.
        A semibrick is a set of pair-wise Hom-orthogonal bricks.
        We only consider basic objects, that is,
        indecomposable summands are pairwise distinct.

        Note that the terminology "semibrick" is usually used only for
        an abelian category.

        Returns:
            list[frozenset[T]]: The list of semibricks.
            Each semibrick is represented by the frozenset of bricks.
        """
        return self.orthogonals(self.is_hom_orthogonal, self.bricks())

    def h_vector(self) -> list[int]:
        """Return the vector counting the cardinalities of semibricks.
        This is [a_0, a_1, a_2, ....] if there are a_i semibricks with
        cardinality i.

        The name "h-vector" comes from the fact that if we consider
        the module category, then this vector is the h-vector of a simplicial
        complex called a support tau-tilting complex.
        Also this counts wide subcategories with given number of simples.
        """
        numbers = [len(SS) for SS in self.semibricks()]
        vector = []
        for i in range(max(numbers)+1):
            vector.append(numbers.count(i))
        return vector

    # --- Methods related to module (abelian) categories ---

    def is_quasi_abelian(self) -> bool:
        """Return whether `self` is the AR quiver of some quasi-abelian category.
        Our category is quasi-abelian if and only if it is equivalent to
        some torsion class (or torsion-free class) of the module category of some
        finite-dimensional algebra, since there're only finitely many indecomposables.

        Algorithm: [Iy3, Theorem 4.4]
        """
        injectives: list[T] = self.injectives()
        supp_inj: set[T] = set()
        for inj in injectives:
            supp_I = set(itertools.chain.from_iterable(
                self.radical_layer(inj)))
            supp_inj = supp_inj | supp_I
        print(supp_inj)
        return set(self.vertices) == supp_inj

    def is_abelian(self) -> bool:
        """Return whether `self` is the AR quiver of some abelian category.
        Since there are only finitely many indecomposables in our category,
        if `self` is abelian, then it has enough projectives, thus it is
        equivalent to the category of finitely generated modules
        over some finite-dimensional k-algebra.

        FIXME: This is not implemented now, hence always returns True.
        """
        return True

    def torsion_pairs(self, check: bool = False):
        """Return the set of all torsion pairs (T, F) for the abelian setting.
        """
        if check and not self.is_abelian():
            raise ValueError("This category is not abelian!")
        return [(self.torsion_closure(S), self.hom_perp_right(S))
                for S in self.semibricks()]

    def torsion_classes(self) -> list[frozenset[T]]:
        """Return the set of all torsion classes for the abelian setting.
        A torsion class is a subcategory of an abelian category
        which is closed under extensions and quotients.
        This works only for an abelian category.
        
        This uses semibricks to reduce computations.
        """
        return [self.hom_perp_left(S) for S in self.semibricks()]

    def torsion_free_classes(self) -> list[frozenset[T]]:
        """Return the set of all torsion-free classes for the abelian setting.
        A torsion-free class is a subcategory of an abelian category
        which is closed under extensions and subobjects.
        This works only for an abelian category.

        This uses semibricks to reduce computations.
        """
        return [self.hom_perp_right(S) for S in self.semibricks()]

    def torsion_poset_lower_dic(self) -> dict[frozenset[T], list[frozenset[T]]]:
        """Return the map which sends each torsion class to the set of
        torsion classes covered by it.
        This contains the information of the Hasse quiver.
        """
        lower_dict = {TT: [TT & self.hom_perp_left([S])
                           for S in self.tors_to_sbrick()[TT]]
                      for TT in self.torsion_classes()}
        return lower_dict

    def torsion_closure(self, M: Collection[T]):
        """Return the smallest torsion class containing `M`.
        """
        return self.hom_perp_left(self.hom_perp_right(M))

    def torsion_free_closure(self, M: Collection[T]):
        """Return the smallest torsion-free class containing `M`.
        """
        return self.hom_perp_right(self.hom_perp_left(M))

    @cache
    def tors_to_sbrick(self):
        """There's a bijection between semibricks and torsion classes
        by taking the torsion closure.
        This gives a dictionary for this bijection,
        sending each torsion class to the corresponding semibrick.
        """
        return {self.torsion_closure(S): S for S in self.semibricks()}

    def _minus_tors(self, TT: frozenset[T]) -> frozenset[T]:
        """Inner method (for now).
        This sends each torsion class TT to a torsion class TT^-,
        which is the smallest torsion class such that [TT^-, TT] is
        a wide interval.
        TT^- is the intersection of all torsion classes covered by TT.
        Useful for computing wide subcategories etc.
        """
        S = self.tors_to_sbrick()[TT]
        return TT & self.hom_perp_left(S)

    def tors_to_wide(self):
        """There is a bijection between torsion classes and wide subcategories
        by sending each wide subcategory to its torsion closure.
        This gives a dictionary for this bijection,
        sending each torsion class to the corresponding wide subcategory."""
        return {TT: TT & self.hom_perp_right(self._minus_tors(TT))
                for TT in self.torsion_classes()}

    def wide_subcategories(self) -> list[frozenset[T]]:
        """Return the set of all wide subcategories.
        A wide subcategory is a subcategory of an abelian category
        which is closed under extensions, kernels, and cokernels.
        
        We compute it by using torsion classes and wide intervals, c.f. [AP].
        """
        return list(self.tors_to_wide().values())

    def ICE_closed_subcategories(self) -> set[frozenset[T]]:
        """Return the set of all ICE-closed subcategory.
        An ICE-closed subcategory is a subcategory of an abelian category
        which is closed under Images, Cokernels, and Extensions.
        
        We compute it by using torsion classes and ICE intervals, see [ES].
        """
        result = set()
        for TT in self.torsion_classes():
            TT_minus = self._minus_tors(TT)
            for UU in self.torsion_classes():
                if TT_minus <= UU <= TT:
                    result.add(UU & self.hom_perp_right(TT_minus))
        return result

    def IKE_closed_subcategories(self) -> set[frozenset[T]]:
        """Return the set of all IKE-closed subcategory.
        An ICE-closed subcategory is a subcategory of an abelian category
        which is closed under Images, Kernels, and Extensions.
        
        We compute it by using torsion classes and IKE intervals, see [ES].
        """

        result = set()
        for TT in self.torsion_classes():
            TT_minus = self._minus_tors(TT)
            for UU in self.torsion_classes():
                if TT_minus <= UU <= TT:
                    result.add(TT & self.hom_perp_right(UU))
        return result

    def torsion_hearts(self) -> set[frozenset[T]]:
        """Return the set of all torsion hearts.
        For two torsion classes UU and TT in an abelian category
        with UU contained in TT, its torsion heart is TT \cap UU^\perp.
        All ICE-closed and IKE-closed, thus torsion(-free) and wide subcats
        are torsion hearts.
        See [En] for details.
        """
        result = set()
        for TT in self.torsion_classes():
            for UU in self.torsion_classes():
                if UU <= TT:
                    result.add(TT & self.hom_perp_right(UU))
        return result

    def IE_closed_subcategories(self) -> set[frozenset[T]]:
        """Return the set of all IE-closed subcategory.
        An IE-closed subcategory is a subcategory of an abelian category
        which is closed under Images and Extensions.
        It is known that a subcategory is IE-closed if and only if
        it is an intersection of some torsion class and some torsion-free class.
        The computation is due to this fact.
        """
        return {TT & FF
                for TT in self.torsion_classes()
                for FF in self.torsion_free_classes()}

    def IE_closure(self, M):
        """Return the smallest IE-closed subcategory containing `M`."""
        return self.torsion_closure(M) & self.torsion_free_closure(M)

    def ext_projectives(self, subcat: Collection[T]) -> list[T]:
        """Return the set of all Ext-projective objects in `subcat`.
        For a given subcategory C, its Ext-projective object is an object P
        satisfying Ext^1(P, C) = 0.
        """
        result: list[T] = []
        for X in subcat:
            vanish = True
            for Y in subcat:
                if self.ext(X, Y) != 0:
                    vanish = False
                    break
            if vanish:
                result.append(X)
        return result

    def ext_injectives(self, subcat: Collection[T]) -> list[T]:
        """Return the set of all Ext-injective objects in `subcat`.
        For a given subcategory C, its Ext-projective object is an object P
        satisfying Ext^1(P, C) = 0.
        """
        result: list[T] = []
        for Y in subcat:
            vanish = True
            for X in subcat:
                if self.ext(X, Y) != 0:
                    vanish = False
                    break
            if vanish:
                result.append(Y)
        return result

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

    def _shift(self, X: T) -> T:
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

    def _shift_neg(self, X: T) -> T:
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

    def shift(self, X: T, n: int = 1) -> T:
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
        else:  # n < 0
            for _ in range(-n):
                result = self._shift_neg(result)
            return result

    def Serre_functor(self, X: T) -> T:
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

    def is_ext_orthogonal(self, X: T, Y: T, degrees: list[int] = [1]) -> bool:
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
        if not self.is_stable():
            raise NotImplementedError("Only works for tri. cat. now.")
        for n in degrees:
            if self.hom(X, self.shift(Y, n)) != 0:
                return False
            elif self.hom(Y, self.shift(X, n)) != 0:
                return False
        return True

    def maximal_ext_orthogonals(self,
                                degrees: list[int] = [1]) -> list[frozenset[T]]:
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

    def ext_orthogonals(self, degrees: list[int] = [1]) -> list[frozenset[T]]:
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
        if not self.is_stable():
            raise ValueError("Your translation quiver should be stable!")
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
