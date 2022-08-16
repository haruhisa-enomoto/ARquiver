"""A program to work with AR quiver and compute various objects.
This uses PySimpleGUI for GUI implementation.

The purpose of this program is to input AR quiver in several ways,
and calculate various objects from it.

Actual computation is achieved by `ARquiver.py`and its class
`TranslationQuiver`, hence the main aim of this program is to provide
a GUIinterface for `ARquiver.py`.

GitHub Repository:
https://github.com/haruhisa-enomoto/ARquiver
"""
from __future__ import annotations
import pickle
import re
import webbrowser

import PySimpleGUI as sg

from ARquiver import TranslationQuiver
from Drawings import *

version = "0.3.0"


# ----- Global variables -----

vertices: list[Vertex] = []
arrows: list[Arrow] = []  # contains both usual arrows and tau arrows.
quiver = None  # `TranslationQuiver` object.

file_path = None
changed: bool = False

# usual_color, border_color, select_color = "gray90", "gray20", "lightsalmon"
# cat_color1, cat_color2 = "CadetBlue1", "light pink"


# ----- Long texts needed in layouts in windows -----


assump_text = """
--- Assumption on your category ---

We fix an algebraically closed field k.
We assume that your translation quiver is the Auslander-Reiten quiver of some k-category C,
which satisfies the following conditions]

1. C is Hom-finite over k and idempotent complete,
    and has only finitely many indecomposables up to isomorphism.
2. C is a tau-category in the sense of Iyama.

Under the condition 1, here are some examples of tau-categories.
- mod A for a finite-dimensional k-algebra A.
- Torsion classes (or torsion-free classes) of mod A.
- Stable category of mod A (or actually any ideal quotient by some additive subcategory).
- Triangulated categories (e.g. cluster categories of Dynkin type).
- The stable category of a Hom-finite Krull-Schmidt extriangulated category with enough projectives [INP].
- The stable category of a Cohen-Macaulay order over a complete CM local ring R (containing our base field) [Iy3].
- The ideal quotient of a tau-category by an additive subcategory [Iy2, 1.4.(2)].
- Mesh categories of translation quivers [Iy1, 8.4].
"""

info_text = (
    """AR quiver calculator ver"""
    + version
    + """

This program is written in Python, and uses PySimpleGUI.
Actually, the actual computation algorithm is written in another module
`ARquiver`, and what this program does is only to provide a framework to
input the translation quiver in GUI.
Source codes of this and `ARquiver` are available in GitHub.

Author: Haruhisa Enomoto
"""
)

ref_text = """
[AP] S. Asai, C. Pfeifer, Wide subcategories and lattices of torsion classes,
    arXiv:1905.01148.

[En] H. Enomoto, From the lattice of torsion classes to the posets
    of wide subcategories and ICE-closed subcategories, arXiv:2201.00595.


[ES] H. Enomoto, A. Sakai, ICE-closed subcategories and wide $\tau$-tilting modules,
    Math. Z. 300 (2022), no. 1, 541--577.

[Iy1] O. Iyama, tau-categories I: Ladders,
    Algebr. Represent. Theory 8 (2005), no. 3, 297--321.

[Iy2] O. Iyama, tau-categories II: Nakayama pairs and Rejective subcategories,
    Algebr. Represent. Theory 8 (2005), no. 4, 449--477.

[Iy3] O. Iyama, The relationship between homological properties
    and representation theoretic realization of artin algebras,
    Trans. Amer. Math. Soc. 357 (2005), no. 2, 709--734.

[INP] O. Iyama, H. Nakaoka, Y. Palu,
    Auslander-Reiten theory in extriangulated categories, arXiv:1805.03776.
"""

alg_text = """
--- dim Hom(X,Y) ---
Our method is based on the computation of so-called ladders for tau-categories in [Iy1, 7.2],
which gives an algorithm to compute the minimal projective presentation of J^n(-,Y) for given Y,
where J is the Jacobson radical.

--- dim Ext^1(X,Y) ---
Based on the AR duality on an extriangualted category [INP].
By the AR duality, computing Ext^1 is reduced to compute stable Hom,
and the stable category is a tau-category, so we can compute it.

--- Subcategories of the module category ---
Since we can compute Hom, we can list all semibricks and Hom-perpendicular categories.
Thus we can list all torsion(-free) classes.
Other classes can be computed from torsion classes as follows:
- Wide subcats: using [AP].
- ICE-closed (or IKE-closed) subcats: using [ES].
- IE-closed subcats: they are precisely intersections of torsion classes and torsion-free classes.

--- Shift functor on triangulated category ---
If C is triangulated, then it has AR triangles, so has a Serre functor S.
It is well-known that S is a composition of tau and shift.
Thus Hom(-, tau X[1]) = D Hom(X, -), so Hom(-, X[1]) = D Hom(tau^{-1}X, -).
If we consider modules over C, then Hom(-, X[1]) has a simple top X[1],
thus by the above duality, X[1] is the socle of a projective module Hom(tau^{-1}X, -).
Therefore, we compute the socle of Hom(tau^{-1}X, -) using radical layer.
"""

subcats_text = """
We can calculate the following classes of subcategories of the module category:

- Torsion(-free) classes: subcategories closed under extensions and quotients (resp. submodules).
- Wide subcategories: subcategories closed under extensions, kernels, and cokernels.
- Semibricks: pair-wise Hom-orthogonal brick (brick: module with End = k
- ICE-closed subcategories: closed under Images, Cokernels, and Extensions.
- IKE-closed subcategories: closed under Images, Kernels, and Extensions.
- Torsion hearts: T \cap U^\perp for some torsion classes U and T with U \subseteq T.
- IE-closed subcategories: closed under Images and Extensions.
"""

tri_text = """
In this tab, we assume your category is a triangulated category with shift functor Sigma.
Ext^n(X, Y) is defined by Hom(X, Sigma^n Y) for an integer n.
"""

tri_ortho_text = """
We list all objects M in your tri. cat. s.t. Ext^n(M, M) = 0 for a given (possibly several) n.
NOTE: 0 object corresponds to the empty list and counted!
"""

module_text = """
In this tab, we assume your category is the module category of a finite-dimensional algebra over a field.
We compute all subcategories satisfying some conditions,
and for a selected subcategory C, we compute its Ext-projective (injective) objects, that is, an object P with Ext^1(P, C) = 0.
For the definitions of the classes of subcategories, see [Help] - [Classes of subcategories].
"""


# -----GUI Layout START-----

sg.theme("DarkGrey2")

vtx_col = [
    [sg.T("Vertices:")],
    [
        sg.Listbox(
            [],
            size=(30, 3),
            key="-vtx-list-",
            select_mode=sg.LISTBOX_SELECT_MODE_MULTIPLE,
        )
    ],
    [sg.T("Add vertices (input vertices separated by space)")],
    [
        sg.Input(key="-vtx-form-", size=(30, 1), do_not_clear=False),
        sg.B("Add", key="-add-vtx-"),
    ],
    [sg.T("Delete selected ones"), sg.B("Delete", key="-del-vtx-")],
]

arrow_col = [
    [sg.T("Arrows:")],
    [
        sg.Listbox(
            [],
            size=(30, 3),
            key="-arrow-list-",
            select_mode=sg.LISTBOX_SELECT_MODE_MULTIPLE,
        )
    ],
    [
        sg.T(
            'Add arrows (input "1 2" to add arrow from 1 to 2,\n'
            'and "1 2 3" to add two arrows 1->2->3)'
        )
    ],
    [
        sg.Input(key="-arrow-form-", size=(30, 1), do_not_clear=False),
        sg.B("Add", key="-add-arrow-"),
    ],
    [sg.T("Delete selected ones"), sg.B("Delete", key="-del-arrow-")],
]

tau_col = [
    [sg.T("AR translations:")],
    [
        sg.Listbox(
            [],
            size=(30, 3),
            key="-tau-list-",
            select_mode=sg.LISTBOX_SELECT_MODE_MULTIPLE,
        )
    ],
    [
        sg.T(
            "Add translation\n"
            '(input "1 2" if tau(1) = 2,'
            '"1 2 3" for tau(1) = 2, tau(2) = 3)'
        )
    ],
    [
        sg.Input(key="-tau-form-", size=(30, 1), do_not_clear=False),
        sg.B("Add", key="-add-tau-"),
    ],
    [sg.T("Delete selected ones"), sg.B("Delete", key="-del-tau-")],
]

col = [
    [sg.T("Choose operations (click for add vertices)")],
    [sg.R("Un/Select vertices", 1, default=True, key="-select-vx-")],
    [sg.R("Move selected", 1, key="-move-selected-")],
    [sg.R("Draw a usual arrow", 1, key="-arrow-")],
    [sg.R("Draw a translation arrow = tau", 1, key="-tau-")],
    [sg.R("Delete item", 1, key="-erase-")],
    [sg.R("Move", 1, key="-move-")],
    [sg.R("Move All", 1, key="-moveall-")],
    [
        sg.R(
            "Align tau-orbit (not recommend for stable tau-orbit)",
            1,
            key="-align-tau-orbit-",
        )
    ],
    [
        sg.Slider(range=(1, 200), default_value=100, orientation="h", key="-scale-"),
        sg.B("Rescale (%)", key="-scale-B-"),
    ],
    [sg.B("Clear")],
]

subcat_col = [
    [sg.T("The number of subcats is"), sg.T("", key="-mod-num-")],
    [sg.T("Choose one! (blue color)")],
    [
        sg.Listbox(
            [],
            size=(30, 10),
            key="-mod-subcat-",
            enable_events=True,
            horizontal_scroll=True,
            expand_x=True,
            expand_y=True,
        )
    ],
    [sg.T("Number of indecs:"), sg.T("", key="-mod-subcat-num-")],
]

size = (70, 80)
# initial size of the canvas. Small value for small environments.
bottom_right_corner = size
# We use the following coordinate system.
# - The top left corner is (0,0)
# - The "initial" bottom right corner is `bottom_right_corner`
# Although the Canvas extends in x and y directions,
# it seems that the initial bottom right corner is remembered,
# and the coordinate does not changes.

input_layout = [
    [sg.Col(vtx_col), sg.Col(arrow_col), sg.Col(tau_col)],
    [
        sg.Graph(
            canvas_size=size,
            graph_bottom_left=(0, bottom_right_corner[1]),
            graph_top_right=(bottom_right_corner[0], 0),
            key="-graph-",
            enable_events=True,
            background_color="white",
            drag_submits=True,
            float_values=True,
            expand_x=True,
            expand_y=True,
        ),
        sg.Col(col),
    ],
    [sg.B("Fit size"), sg.B("Done!")],
]

hom_layout = [
    [
        sg.T(
            "Let's compute dim_k Hom(X,Y) and Ext^1(X, Y).\n"
            "Click or select X (blue) and Y (red) in the quiver."
        )
    ],
    [
        sg.Graph(
            canvas_size=size,
            graph_bottom_left=(0, bottom_right_corner[1]),
            graph_top_right=(bottom_right_corner[0], 0),
            key="-hom-graph-",
            enable_events=True,
            background_color="white",
        )
    ],
    [
        sg.T("X = "),
        sg.Combo([], size=(5, 1), key="-hom-X-", enable_events=True),
        sg.T("Y = "),
        sg.Combo([], size=(5, 1), key="-hom-Y-", enable_events=True),
        sg.B("Compute!", key="-hom-B-"),
        sg.T("dim_k Hom(X,Y) = "),
        sg.T("", key="-hom-out-"),
        sg.T(", dim_k Ext^1(X,Y) = "),
        sg.T("", key="-ext-out-"),
    ],
    [
        sg.T("The radical series of Hom(X,-) is"),
        sg.Listbox([], size=(10, 5), expand_x=True, key="-hom-cov-"),
        sg.T("The radical series of Hom(-,Y) is"),
        sg.Listbox([], size=(10, 5), expand_x=True, key="-hom-cont-"),
    ],
]

tri_shift_layout = [
    [sg.T("1. Compute Sigma^n")],
    [
        sg.T("Click or select an object in the quiver."),
        sg.Combo([], size=(5, 1), key="-tri-X-", enable_events=True),
        sg.T("n = (default 1)"),
        sg.Input(size=(5, 1), key="-tri-shift-deg-"),
        sg.B("Apply Sigma^n!", key="-tri-shift-B-"),
        sg.T("", key="-tri-shift-in-"),
        sg.T(" goes to "),
        sg.T("", key="-tri-shift-out-"),
    ],
    [
        sg.Graph(
            canvas_size=size,
            graph_bottom_left=(0, bottom_right_corner[1]),
            graph_top_right=(bottom_right_corner[0], 0),
            key="-tri-graph-",
            background_color="white",
            enable_events=True,
        )
    ],
    [sg.T("2. Objectwise period of shift functor")],
    [
        sg.T("The period of the action of Sigma on objects:"),
        sg.B("Compute!", key="-tri-per-B-"),
        sg.T("", key="-tri-per-out-"),
    ],
]

tri_ortho_col = [
    [sg.T("Consider maximal objects with Ext vanishes.")],
    [sg.T("The number of such basic objects is"), sg.T("", key="-tri-ortho-num1-")],
    [sg.T("Choose one! (blue color)")],
    [
        sg.Listbox(
            [],
            size=(30, 5),
            key="-tri-ortho-out1-",
            enable_events=True,
            horizontal_scroll=True,
            expand_x=True,
            expand_y=True,
        )
    ],
    [sg.T("Number of indec summands:"), sg.T("", key="-tri-ortho-ind-num1-")],
    [
        sg.T(
            "Without the maximality condition,\n"
            "the number of basic orthogonal objects is:"
        )
    ],
    [sg.T("", key="-tri-ortho-num2-")],
]

tri_ortho_layout = [
    [sg.T(tri_ortho_text)],
    [
        sg.T(
            "Input n s.t. you want Ext^n to vanish."
            "(default: 1)\n"
            "Input like '1 2 3' if you want Ext^1, "
            "Ext^2 and Ext^3 to vanish."
        ),
        sg.Input(size=(30, 1), key="-tri-deg-"),
        sg.B("Compute!", key="-tri-ortho-B-"),
    ],
    [
        sg.Graph(
            canvas_size=size,
            graph_bottom_left=(0, bottom_right_corner[1]),
            graph_top_right=(bottom_right_corner[0], 0),
            key="-tri-ortho-graph-",
            background_color="white",
        ),
        sg.Col(tri_ortho_col),
    ],
]

tri_layout = [
    [sg.T(tri_text)],
    [
        sg.TabGroup(
            [
                [
                    sg.Tab("Shift functor", tri_shift_layout),
                    sg.Tab("Maximal Ext-orthogonals", tri_ortho_layout),
                ]
            ],
            expand_x=True,
            expand_y=True,
        )
    ],
]

module_layout = [
    [sg.T(module_text)],
    [
        sg.T("Compute all"),
        sg.Combo(
            [
                "torsion classes",
                "torsion-free classes",
                "semibricks",
                "wide subcategories",
                "ICE-closed subcategories",
                "IKE-closed subcategories",
                "torsion hearts",
                "IE-closed subcategories",
                "IE-closed, not torsion hearts",
            ],
            default_value="torsion classes",
            auto_size_text=True,
            readonly=True,
            key="-mod-sel-",
        ),
        sg.B("Compute", key="-mod-B-"),
    ],
    [
        sg.Graph(
            canvas_size=size,
            graph_bottom_left=(0, bottom_right_corner[1]),
            graph_top_right=(bottom_right_corner[0], 0),
            key="-mod-graph-",
            background_color="white",
        ),
        sg.Col(subcat_col),
    ],
    [sg.T("Select a subcategory.")],
    [
        sg.R("Ext-projectives", 2, default=True, key="-proj-"),
        sg.R("Ext-injectives", 2, key="-inj-"),
        sg.B("Compute", key="-ext-obj-B-"),
        sg.T("", key="-ext-obj-out-"),
        sg.T("(shown in red)"),
    ],
]

menu_def = [
    [
        "&File",
        [
            "&New",
            "&Open",
            "&Save",
            "Save &As...",
            "---",
            "&Import from String Applet",
            "&Export",
            ["Export the translation quiver data", "Export the tex (not implemented!)"],
            "---",
            "E&xit",
        ],
    ],
    [
        "Help",
        [
            "About this program",
            "---",
            "Assumptions",
            "How it works",
            "---",
            "Classes of subcategories",
            "---",
            "References",
        ],
    ],
]

layout = [
    [sg.Menu(menu_def)],
    [
        sg.TabGroup(
            [
                [
                    sg.Tab("Input", input_layout),
                    sg.Tab("Compute Hom and Ext^1", hom_layout),
                    sg.Tab("Module categories", module_layout),
                    sg.Tab("Triangulated categories", tri_layout),
                ]
            ],
            expand_x=True,
            expand_y=True,
        )
    ],
]

window_title = "AR quiver calculator ver. " + version
window = sg.Window(
    window_title,
    layout,
    resizable=True,
    finalize=True,
    enable_close_attempted_event=True,
)
# window.maximize()

graph: sg.Graph = window["-graph-"]
hom_graph: sg.Graph = window["-hom-graph-"]
mod_graph: sg.Graph = window["-mod-graph-"]
tri_graph: sg.Graph = window["-tri-graph-"]
tri_ortho_graph: sg.Graph = window["-tri-ortho-graph-"]
str_to_graph = {
    "main": graph,
    "hom": hom_graph,
    "mod": mod_graph,
    "tri": tri_graph,
    "tri_ortho": tri_ortho_graph,
}

# -----GUI Layout END-----

dragging = False
drawing_arrow = False
selecting_X = False
X_vtx = None
Y_vtx = None
tri_vtx = None
vertex_keys = ["-hom-X-", "-hom-Y-", "-tri-X-"]

# -----Some functions to draw AR quivers-----


def draw_arrow(source: Vertex, target: Vertex, tau: bool = False) -> None:
    """
    Draw an arrow from `source` to `target`, construct an instance of `Arrow`,
    and add it to `arrows`.
    """
    arrow = Arrow(source, target, str_to_graph, tau)
    arrow.draw()
    arrows.append(arrow)


def draw_vertex(name: str, location: tuple[float, float]) -> None:
    """
    Draw a vertex in position, construct an instance of Vertex,
    and add it to `vertices`.
    """
    vertex = Vertex(name, location, str_to_graph)
    vertex.draw()
    vertices.append(vertex)


def delete_vertex(vertex: Vertex) -> None:
    """
    Delete `vertex` and its related arrows from the canvas,
    and also remove them from `vertices` and `arrows`.
    """
    global drawing_arrow
    vertex.delete()
    if drawing_arrow:
        graph.TKCanvas.itemconfig(source_vtx.circle_id["main"], fill="gray20")
        drawing_arrow = False
    vertices.remove(vertex)
    search_arrow_con = [a for a in arrows if vertex in (a.source, a.target)]
    for arrow in search_arrow_con:
        arrow.delete()
        arrows.remove(arrow)


# not used currently
# def location_of_fig(figure: int) -> tuple[float, float]:
#     """
#     Return the coordinate (x,y) of the center of `figure`.
#     """
#     (x1, y1), (x2, y2) = graph.get_bounding_box(figure)
#     return ((x1 + x2) / 2, (y1 + y2) / 2)


def add_vtx_from_form(lst: list[str]) -> None:
    """
    Add vertices from input form
    and draw the corresponding vertex in the figure.
    """
    names = [v.name for v in vertices]
    lst = sorted(list(set(names + lst) - set(names)))
    # Only add new vertices

    size: tuple[float, float] = graph.get_size()

    i = 1
    for vtx in lst:
        N = len(lst) + 1
        draw_vertex(vtx, (i / N * size[0], size[1] / 2))
        i = i + 1
    update_info()


def fit_size() -> None:
    """
    Adjust locations of all vertices to fit the current canvas.
    """
    if not vertices:
        return
    canvas_size: tuple[float, float] = graph.get_size()
    min_x = min([vtx.location[0] for vtx in vertices])
    min_y = min([vtx.location[1] for vtx in vertices])
    max_x = max([vtx.location[0] for vtx in vertices])
    max_y = max([vtx.location[1] for vtx in vertices])
    width = max_x - min_x
    height = max_y - min_y
    if width == 0:
        width = canvas_size[0]
    if height == 0:
        height = canvas_size[1]
    for vtx in vertices:
        x, y = vtx.location
        new_x = 30 + (x - min_x) / width * (canvas_size[0] - 60)
        new_y = 30 + (y - min_y) / height * (canvas_size[1] - 60)
        vtx.location = new_x, new_y
        vtx.draw()
    for ar in arrows:
        ar.delete()
        ar.draw()


def unselect_all(graph_name: str = "main"):
    for v in vertices:
        v.unselect(graph_name)


def vertex_from_drag(drag_figures, graph_name: str = "main"):
    if len(drag_figures) == 0:
        return None
    figure = drag_figures[-1]
    search = [
        v
        for v in vertices
        if figure in (v.circle_id[graph_name], v.label_id[graph_name])
    ]
    return search[0] if search else None


def tau_orbit(v):
    tau, tauinv = {}, {}
    for ar in arrows:
        if ar.is_tau:
            tau[ar.source.name] = ar.target.name
            tauinv[ar.target.name] = ar.source.name

    # yield tau-orbit of v
    tauinvs = [v.name]
    uname, flag = v.name, True
    while uname in tauinv and flag:  # should be made more functorial
        uname = tauinv[uname]
        tauinvs.append(uname)
        flag = uname != tauinvs[0]  # false if stable orbit

    vxdict = {u.name: u for u in vertices}  # just for easy access
    Ov = []
    if not flag:
        Ov = [vxdict[un] for un in tauinvs]
    else:
        uname, taus = v.name, []
        while uname in tau:
            uname = tau[uname]
            taus.append(uname)
        taus.reverse()
        # print("tau orbit: ", taus+tauinvs)
        Ov = [vxdict[un] for un in taus + tauinvs]
    return Ov


def spread_vertices_over_span(
    vxs: list[Vertex], startx: float, endx: float, y: float
) -> None:
    if len(vxs) <= 1:
        return
    interval = (endx - startx) / (len(vxs) - 1)
    for i, u in enumerate(vxs):
        u.location = (startx + interval * i, y)
        u.select()
        # u.draw()
    for ar in arrows:
        ar.delete()
        ar.draw()


def update_info() -> None:
    """
    Update the displayed information about the AR quiver.
    """
    vertices_list = sorted(vertices)
    arrows_list = sorted([ar for ar in arrows if not ar.is_tau])
    tau_list = sorted([ar for ar in arrows if ar.is_tau])
    window["-vtx-list-"].update(values=vertices_list)
    window["-arrow-list-"].update(values=arrows_list)
    window["-tau-list-"].update(values=tau_list)


def make_new_window(window_key: str) -> None:
    """
    Make the new window (modal) for info, references, etc, and wait for events.
    """
    if window_key == "About this program":
        layout = [
            [sg.T(info_text)],
            [sg.B("Author's website", key="-WEB-"), sg.B("GitHub"), sg.OK()],
        ]

    elif window_key == "References":
        layout = [[sg.T(ref_text)], [sg.OK()]]

    elif window_key == "How it works":
        layout = [[sg.T(alg_text)], [sg.OK()]]

    elif window_key == "Assumptions":
        layout = [[sg.T(assump_text)], [sg.OK()]]

    elif window_key == "Classes of subcategories":
        layout = [[sg.T(subcats_text)], [sg.OK()]]

    else:
        raise ValueError

    new_window = sg.Window(window_key, layout, modal=True)
    while True:
        event, _ = new_window.read()
        if event in (sg.WIN_CLOSED, "OK"):
            break
        elif event == "-WEB-":
            webbrowser.open_new("https://haruhisa-enomoto.github.io/")
        elif event == "GitHub":
            webbrowser.open_new("https://github.com/haruhisa-enomoto/ARquiver")

    new_window.close()


def complete_warning():
    sg.popup("Please click 'Done!' button in 'Input' Tab.", title="Error")


# -----Event Loop-----
while True:
    event: str
    values: dict
    event, values = window.read()
    # print(event, values, "\n____")

    if event == sg.WIN_CLOSE_ATTEMPTED_EVENT and not changed:
        break

    elif (
        event == sg.WIN_CLOSE_ATTEMPTED_EVENT
        and sg.popup_yes_no("Are you sure to discard changes?", title="Warning")
        == "Yes"
    ):
        break

    elif event == "Clear":
        if vertices:
            changed = True
        graph.erase()
        vertices, arrows = [], []
        update_info()

    elif event == "-add-vtx-":
        changed = True
        add_vtx_from_form(values["-vtx-form-"].split())
        update_info()

    elif event == "-add-arrow-":
        data = values["-arrow-form-"].split()
        if len(data) < 2:
            sg.popup("Please input like '1 2' for 1->2.", title="Error")
            continue
        changed = True
        # First add new vertices if needed
        names = [v.name for v in vertices]
        new_names = list(set([x for x in data if x not in names]))
        add_vtx_from_form(new_names)
        for i in range(len(data) - 1):
            source_name, target_name = data[i : i + 2]
            source = [v for v in vertices if v.name == source_name][0]
            target = [v for v in vertices if v.name == target_name][0]
            draw_arrow(source, target)
        update_info()

    elif event == "-add-tau-":
        data = values["-tau-form-"].split()
        if len(data) < 2:
            sg.popup("Please input like '1 2' for tau(1)=2.", title="Error")
            continue
        changed = True
        # First add new vertices if needed
        names = [v.name for v in vertices]
        new_names = [x for x in data if x not in names]
        add_vtx_from_form(new_names)
        for i in range(len(data) - 1):
            source_name, target_name = data[i : i + 2]
            source = [v for v in vertices if v.name == source_name][0]
            target = [v for v in vertices if v.name == target_name][0]
            draw_arrow(source, target, tau=True)
        update_info()

    elif event == "-del-vtx-":
        changed = values["-vtx-list-"] != []
        for v in values["-vtx-list-"]:
            delete_vertex(v)
        update_info()

    elif event == "-del-arrow-":
        changed = values["-arrow-list-"] != []
        for ar in values["-arrow-list-"]:
            ar.delete()
            arrows.remove(ar)
        update_info()

    elif event == "-del-tau-":
        changed = values["-tau-list-"] != []
        for ar in values["-tau-list-"]:
            ar.delete()
            arrows.remove(ar)
        update_info()

    elif event == "-graph-":
        x: float
        y: float
        x, y = values["-graph-"]
        if not dragging:
            dragging = True
            drag_figures = graph.get_figures_at_location((x, y))
            last_xy = x, y
            first_time = True
        else:
            first_time = False
        delta_x, delta_y = x - last_xy[0], y - last_xy[1]
        last_xy = x, y

        if values["-align-tau-orbit-"]:
            v = vertex_from_drag(drag_figures)
            if v is None:
                continue
            unselect_all()  # needs to be after v = vertex_from_drag
            Ov = tau_orbit(v)
            xs = [u.location[0] for u in Ov]
            min_x, max_x = min(xs), max(xs)
            if Ov[0] == Ov[len(Ov) - 1]:  # stable tau-orbit, may want special handling
                Ov.pop()
            if len(Ov) > 1:
                spread_vertices_over_span(Ov, min_x, max_x, v.location[1])

        elif values["-moveall-"]:
            changed = True
            graph.move(delta_x, delta_y)
            for vertex in vertices:
                vertex.update_location()

        elif (values["-arrow-"] or values["-tau-"]) and not drag_figures and first_time:
            # Then we add a vertex.
            # First decide the numbering of the vertices,
            # which is the smallest unused number.
            changed = True
            number: int = 1
            unselect_all()

            while True:
                if str(number) not in [v.name for v in vertices]:
                    break
                number = number + 1
            draw_vertex(str(number), (x, y))
            update_info()

        elif (values["-arrow-"] or values["-tau-"]) and drag_figures and first_time:
            # Then draw an arrow.
            is_tau: bool = values["-tau-"]
            # figure: int = drag_figures[-1]
            # search = [
            #     v
            #     for v in vertices
            #     if figure in (v.circle_id["main"], v.label_id["main"])
            # ]
            # # Search a vertex which is clicked.
            # if not search:
            #     continue
            # vertex = search[0]
            vertex = vertex_from_drag(drag_figures)
            unselect_all()
            if not drawing_arrow:
                # Then this vertex is selected as a source.
                source_vtx = vertex
                drawing_arrow = True
                # Change color!
                # graph.TKCanvas.itemconfig(
                #     source_vtx.circle_id["main"], fill=select_color
                # )
                vertex.select()
            else:
                changed = True
                # Then this vertex is a target, and we will draw an arrow.
                draw_arrow(source_vtx, vertex, is_tau)
                source_vtx.unselect()
                # graph.TKCanvas.itemconfig(
                #     source_vtx.circle_id["main"], fill=usual_color
                # )
                drawing_arrow = False
                update_info()

        elif values["-erase-"] and drag_figures:
            figure = drag_figures[-1]
            search_vtx = [
                v
                for v in vertices
                if figure in (v.circle_id["main"], v.label_id["main"])
            ]
            search_arrow = [a for a in arrows if figure == a.figure_id["main"]]
            if search_vtx:
                unselect_all()
                changed = True
                vertex = search_vtx[0]
                delete_vertex(vertex)
            elif search_arrow:
                unselect_all()
                changed = True
                for arrow in search_arrow:
                    arrow.delete()
                    arrows.remove(arrow)
            update_info()

        elif drag_figures:
            # Then move!
            # Code Refactored:
            vertex = vertex_from_drag(drag_figures)
            if values["-move-selected-"]:
                for u in vertices:
                    if u.selected:
                        graph.move_figure(u.circle_id["main"], delta_x, delta_y)
                        graph.move_figure(u.label_id["main"], delta_x, delta_y)
                        u.update_location()
                for ar in arrows:
                    ar.delete()
                    ar.draw()
            else:  # consider merge with "move selected" in some way?
                graph.move_figure(vertex.circle_id["main"], delta_x, delta_y)
                graph.move_figure(vertex.label_id["main"], delta_x, delta_y)
                vertex.update_location()
                search_arrow = [a for a in arrows if vertex in (a.source, a.target)]
                for arrow in search_arrow:
                    arrow.delete()
                    arrows.remove(arrow)
                    draw_arrow(arrow.source, arrow.target, arrow.is_tau)
            graph.update()

    elif event == "-scale-B-":
        changed = values["-scale-"] != 100
        for vertex in vertices:
            ratio: float = values["-scale-"] / 100
            vertex.location = (vertex.location[0] * ratio, vertex.location[1] * ratio)
            vertex.draw()
        for ar in arrows:
            ar.delete()
            ar.draw()
        window["-scale-"].update(100)

    elif event == "-graph-+UP":  # The drawing has ended because mouse up
        dragging = False
        if values["-select-vx-"]:
            v = vertex_from_drag(graph.get_figures_at_location(values["-graph-"]))
            if v is not None:
                v.toggle()

    elif event == "Fit size":
        fit_size()
        changed = True

    elif event == "Done!":
        # Construct an instance of `TranslationQuiver`.
        # Vertices are names (str) of each `Vertex`.
        name_to_vertex = {v.name: v for v in vertices}
        vertices_list = [v.name for v in vertices]
        # First construct a dictionary tau.
        tau = {ar.source.name: ar.target.name for ar in arrows if ar.is_tau}
        if len(tau) != len([ar for ar in arrows if ar.is_tau]):
            sg.popup("Some tau-arrows have the same codomain!", title="Error")
            continue
        arrow_list = [
            (ar.source.name, ar.target.name) for ar in arrows if not ar.is_tau
        ]
        try:
            quiver = TranslationQuiver(vertices_list, arrow_list, tau)
            sg.popup("Your AR quiver has been successfully inputted!", title="Success!")
            for key in vertex_keys:
                window[key].update(values=vertices)
            # Copy the AR quiver to other tabs
            size = graph.get_size()
            for graph_name, graph_obj in str_to_graph.items():
                if graph_name == "main":
                    continue
                graph_obj.erase()
                graph_obj.set_size((size[0] * 0.9, size[1] * 0.9))
                graph_obj.change_coordinates((0, size[1]), (size[0], 0))
                for v in vertices:
                    v.draw(graph_name)
                for ar in arrows:
                    ar.draw(graph_name)
        except ValueError as e:
            sg.popup(e, title="Error")

    # --- Events on copied graphs

    elif event == "-hom-graph-":
        x: float
        y: float
        x, y = values["-hom-graph-"]
        drag_figures = hom_graph.get_figures_at_location((x, y))
        if not drag_figures:
            continue
        # figure: int = drag_figures[-1]
        # search = [
        #     v for v in vertices if figure in (v.circle_id["hom"], v.label_id["hom"])
        # ]
        # # Search a vertex which is clicked.
        # if not search:
        #     continue
        # vertex = search[0]
        vertex = vertex_from_drag(drag_figures, "hom")
        if not selecting_X:
            # Then this vertex is X s.t. we'll calculate (X,-).
            # Reset previously selected vertices' colors.
            if X_vtx:
                hom_graph.TKCanvas.itemconfig(X_vtx.circle_id["hom"], fill=usual_color)
            if Y_vtx:
                hom_graph.TKCanvas.itemconfig(Y_vtx.circle_id["hom"], fill=usual_color)
            X_vtx = vertex
            hom_graph.TKCanvas.itemconfig(X_vtx.circle_id["hom"], fill=cat_color1)
            window["-hom-X-"].update(X_vtx)
            selecting_X = True
        else:
            Y_vtx = vertex
            hom_graph.TKCanvas.itemconfig(vertex.circle_id["hom"], fill=cat_color2)
            window["-hom-Y-"].update(Y_vtx)
            selecting_X = False

    elif event == "-tri-graph-":
        x: float
        y: float
        x, y = values["-tri-graph-"]
        drag_figures = hom_graph.get_figures_at_location((x, y))
        if not drag_figures:
            continue
        figure: int = drag_figures[-1]
        search = [
            v for v in vertices if figure in (v.circle_id["tri"], v.label_id["tri"])
        ]
        # Search a vertex which is clicked.
        if not search:
            continue
        vertex = search[0]
        # Then this vertex is X s.t. we'll calculate (X,-).
        # Reset previously selected vertices' colors.
        if tri_vtx:
            tri_graph.TKCanvas.itemconfig(tri_vtx.circle_id["tri"], fill=usual_color)
        tri_vtx = vertex
        tri_graph.TKCanvas.itemconfig(tri_vtx.circle_id["tri"], fill=cat_color1)
        window["-tri-X-"].update(tri_vtx)

    # --- Events on Save and open ---

    elif event == "New":
        if (
            changed
            and sg.popup_yes_no("Are you sure to discard changes?", title="Warning")
            == "No"
        ):
            continue
        changed = False
        file_path = None
        graph.erase()
        vertices, arrows = [], []
        window.TKroot.title(window_title)
        update_info()

    elif event == "Save" and file_path:
        with open(file_path, "wb") as f:
            pickle.dump((vertices, arrows), f)
        changed = False

    elif (event == "Save" and not file_path) or event == "Save As...":
        file_path = sg.popup_get_file(
            "Enter a filename.",
            default_extension="pickle",
            file_types=[("Pickle file", "*.pickle"), ("ALL Files", "*.*")],
            save_as=True,
            no_window=True,
        )
        if not file_path:
            continue
        try:
            with open(file_path, "wb") as f:
                pickle.dump((vertices, arrows), f)
            window.TKroot.title(file_path + " - " + window_title)
            changed = False
        except Exception as e:
            sg.popup(e, title="Error")

    elif event == "Open":
        sure = "Yes"
        if changed:
            sure = sg.popup_yes_no("Are you sure to discard changes?", title="Warning")
        if sure == "Yes":
            file_path = sg.popup_get_file(
                "Choose saved data (Current state will be discarded!)",
                title="Open",
                file_types=[("Pickle file", "*.pickle"), ("ALL Files", "*.*")],
                no_window=True,
            )
            if not file_path:
                continue
            try:
                with open(file_path, "rb") as f:
                    vertices, arrows = pickle.load(f)
                    graph.erase()
                    for v in vertices:
                        v.circle_id = {}
                        v.label_id = {}
                        v.str_to_graph = str_to_graph
                        v.selected = False
                        v.draw()
                    for ar in arrows:
                        ar.figure_id = {}
                        ar.str_to_graph = str_to_graph
                        ar.draw()
                    window.TKroot.title(file_path + " - " + window_title)
                    fit_size()  # not sure if I should make changed=True?
                    changed = False
            except Exception as e:
                sg.popup(e, title="Error")
            update_info()

    elif event == "Export the translation quiver data":
        if not quiver:
            complete_warning()
            continue
        file_path = sg.popup_get_file(
            "The created object of a class `TranslationQuiver` "
            "will be saved. Enter a filename.",
            default_extension="pickle",
            file_types=[("Pickle file", "*.pickle")],
            save_as=True,
            no_window=True,
        )
        if file_path:
            try:
                with open(file_path, "wb") as f:
                    pickle.dump(quiver, f)
            except Exception as e:
                sg.popup(e)

    elif event == "Import from String Applet":
        file_path = sg.popup_get_file(
            "Enter your tex file exported from String Applet",
            file_types=[("LaTeX file", "*.tex"), ("ALL Files", "*.*")],
            no_window=True,
        )
        if file_path:
            with open(file_path, "r", encoding="utf-8") as f:
                lines_lst = f.readlines()
            # Cut out the needed part
            begin_str = [line for line in lines_lst if "Auslander" in line][0]
            begin_idx = lines_lst.index(begin_str)
            needed_part = lines_lst[begin_idx:]
            # There are two `scope` environments in the needed part
            # inside the tikzpicture environment.
            # The first one is the set of vertices,
            # and the second one is the set of arrows.
            # scope_count = 1: the first one
            # scope_count = 2: the second one
            scope_count: int = 0
            loaded_vertices: list[tuple[str, tuple[float, float]]] = []
            loaded_arrows: list[tuple[str, str, bool]] = []
            # loaded arrow data is of the form
            # (name of source, name of target, whether it's a tau arrow)
            for line in needed_part:
                if "begin{scope}" in line:
                    scope_count = scope_count + 1
                if scope_count == 0:
                    continue
                elif scope_count == 1:
                    match = re.search(r"node \((.*)\) at", line)
                    if match:
                        vtx_name = match.group(1)
                        location_str = re.search(r"at \((.*)\)", line).group(1)
                        x_str, y_str = location_str.split(",")
                        location = (3 * float(x_str), 3 * float(y_str))
                        loaded_vertices.append((vtx_name, location))
                elif scope_count == 2:
                    match = re.findall(r"\((.+?)\)", line)
                    tau_search = re.search(r"dotted", line)
                    is_tau: bool = False
                    if match:
                        source, target = match[0], match[1]
                        if tau_search:
                            is_tau = True
                        loaded_arrows.append((source, target, is_tau))
                else:
                    break
            vertices, arrows = [], []
            graph.erase()
            for vtx_name, location in loaded_vertices:
                draw_vertex(vtx_name, location)
            for source_name, target_name, is_tau in loaded_arrows:
                source = [v for v in vertices if v.name == source_name][0]
                target = [v for v in vertices if v.name == target_name][0]
                draw_arrow(source, target, is_tau)
            fit_size()
            update_info()

    # --- Event concerning calculations ---

    elif event == "-hom-X-":
        if X_vtx:
            hom_graph.TKCanvas.itemconfig(X_vtx.circle_id["hom"], fill=usual_color)
        X_vtx = values["-hom-X-"]
        hom_graph.TKCanvas.itemconfig(X_vtx.circle_id["hom"], fill=cat_color1)

    elif event == "-hom-Y-":
        if Y_vtx:
            hom_graph.TKCanvas.itemconfig(Y_vtx.circle_id["hom"], fill=usual_color)
        Y_vtx = values["-hom-Y-"]
        hom_graph.TKCanvas.itemconfig(Y_vtx.circle_id["hom"], fill=cat_color2)

    elif event == "-hom-B-":
        if not quiver:
            complete_warning()
            continue
        if X_vtx:
            hom_graph.TKCanvas.itemconfig(X_vtx.circle_id["hom"], fill=usual_color)
        if Y_vtx:
            hom_graph.TKCanvas.itemconfig(Y_vtx.circle_id["hom"], fill=usual_color)
        X_vtx, Y_vtx = values["-hom-X-"], values["-hom-Y-"]
        if not (X_vtx in vertices and Y_vtx in vertices):
            sg.popup("Please select X and Y in the quiver!", title="Error")
            continue
        X, Y = X_vtx.name, Y_vtx.name
        hom_graph.TKCanvas.itemconfig(X_vtx.circle_id["hom"], fill=cat_color1)
        hom_graph.TKCanvas.itemconfig(Y_vtx.circle_id["hom"], fill=cat_color2)
        try:
            window["-hom-out-"].update(quiver.hom(X, Y))
            window["-ext-out-"].update(quiver.ext(X, Y))
            hom_X_layer = quiver.radical_layer(X, contravariant=False)
            hom_Y_layer = quiver.radical_layer(Y)
            window["-hom-cov-"].update(values=hom_X_layer)
            window["-hom-cont-"].update(values=hom_Y_layer)
        except ValueError as e:
            sg.popup(e, title="Error")

    elif event == "-tri-X-":
        if tri_vtx:
            tri_graph.TKCanvas.itemconfig(tri_vtx.circle_id["hom"], fill=usual_color)
        tri_vtx = values["-tri-X-"]
        tri_graph.TKCanvas.itemconfig(tri_vtx.circle_id["hom"], fill=cat_color1)

    elif event == "-tri-shift-B-":
        if not quiver:
            complete_warning()
            continue
        if values["-tri-X-"] not in vertices:
            sg.popup("Please select X in the quiver!", title="Error")
            continue
        X_vtx = values["-tri-X-"]
        X = X_vtx.name
        degree = values["-tri-shift-deg-"]
        if degree:
            try:
                degree = int(degree)
            except ValueError:
                sg.popup("Enter an integer!", title="Error")
                continue
        else:
            degree = 1
        try:
            shift_X = quiver.shift(X, degree)
            window["-tri-shift-in-"].update(X)
            window["-tri-shift-out-"].update(shift_X)
            shift_vtx = name_to_vertex[shift_X]
            tri_graph.TKCanvas.itemconfig(X_vtx.circle_id["hom"], fill=usual_color)
            tri_graph.TKCanvas.itemconfig(shift_vtx.circle_id["hom"], fill=cat_color1)
            window["-tri-X-"].update(shift_vtx)
            tri_vtx = shift_vtx
        except ValueError as e:
            sg.popup(e, title="Error")

    elif event == "-tri-per-B-":
        if not quiver:
            complete_warning()
            continue
        try:
            period = quiver.period()
            window["-tri-per-out-"].update(period)
        except ValueError as e:
            sg.popup(e, title="Error")

    elif event == "-tri-ortho-B-":
        if not quiver:
            complete_warning()
            continue
        try:
            degrees = [int(n) for n in values["-tri-deg-"].split()]
            if not degrees:
                degrees = [1]
            result1 = quiver.maximal_ext_orthogonals(degrees)
            result2 = quiver.ext_orthogonals(degrees)
            maximal_list = [sorted([name_to_vertex[X] for X in CC]) for CC in result1]
            maximal_list.sort(key=lambda T: (len(T), T))
            window["-tri-ortho-out1-"].update(values=maximal_list)
            window["-tri-ortho-num1-"].update(len(maximal_list))
            window["-tri-ortho-num2-"].update(len(result2))
        except Exception as e:
            sg.popup(e, title="Error")

    elif event == "-tri-ortho-out1-" and values["-tri-ortho-out1-"]:
        indec_objs = values["-tri-ortho-out1-"][0]
        window["-tri-ortho-ind-num1-"].update(len(indec_objs))
        for vtx in vertices:
            if vtx in indec_objs:
                tri_ortho_graph.TKCanvas.itemconfig(
                    vtx.circle_id["tri_ortho"], fill=cat_color1
                )
            else:
                tri_ortho_graph.TKCanvas.itemconfig(
                    vtx.circle_id["tri_ortho"], fill=usual_color
                )

    elif event == "-mod-B-":
        if not quiver:
            complete_warning()
            continue
        try:
            if values["-mod-sel-"] == "torsion classes":
                subcats = quiver.torsion_classes()
            elif values["-mod-sel-"] == "torsion-free classes":
                subcats = quiver.torsion_free_classes()
            elif values["-mod-sel-"] == "semibricks":
                subcats = quiver.semibricks()
            elif values["-mod-sel-"] == "wide subcategories":
                subcats = quiver.wide_subcategories()
            elif values["-mod-sel-"] == "IE-closed subcategories":
                subcats = quiver.IE_closed_subcategories()
            elif values["-mod-sel-"] == "ICE-closed subcategories":
                subcats = quiver.ICE_closed_subcategories()
            elif values["-mod-sel-"] == "IKE-closed subcategories":
                subcats = quiver.IKE_closed_subcategories()
            elif values["-mod-sel-"] == "torsion hearts":
                subcats = quiver.torsion_hearts()
            elif values["-mod-sel-"] == "IE-closed, not torsion hearts":
                subcats = quiver.IE_closed_subcategories() - quiver.torsion_hearts()
            else:
                raise ValueError
            subcats_list = [sorted([name_to_vertex[X] for X in CC]) for CC in subcats]
            subcats_list.sort(key=lambda T: (len(T), T))
            window["-mod-num-"].update(len(subcats_list))
            window["-mod-subcat-"].update(values=subcats_list)
        except Exception as e:
            sg.popup(e, title="Error")

    elif event == "-mod-subcat-" and values["-mod-subcat-"]:
        indec_objs = values["-mod-subcat-"][0]
        window["-mod-subcat-num-"].update(len(indec_objs))
        for vtx in vertices:
            if vtx in indec_objs:
                mod_graph.TKCanvas.itemconfig(vtx.circle_id["mod"], fill=cat_color1)
            else:
                mod_graph.TKCanvas.itemconfig(vtx.circle_id["mod"], fill=usual_color)

    elif event == "-ext-obj-B-" and values["-mod-subcat-"]:
        subcat: list[Vertex] = values["-mod-subcat-"][0]
        subcat_names = [v.name for v in subcat]
        if values["-proj-"]:
            obj_names = quiver.ext_projectives(subcat_names)
        else:
            obj_names = quiver.ext_injectives(subcat_names)
        objs: list[Vertex] = []
        for vtx in subcat:
            if vtx.name in obj_names:
                mod_graph.TKCanvas.itemconfig(vtx.circle_id["mod"], fill=cat_color2)
                objs.append(vtx)
            else:
                mod_graph.TKCanvas.itemconfig(vtx.circle_id["mod"], fill=cat_color1)
        objs.sort()
        window["-ext-obj-out-"].update(" ".join([str(v) for v in objs]))

    # --- Event making new window ---

    elif event in (
        "References",
        "About this program",
        "How it works",
        "Assumptions",
        "Classes of subcategories",
    ):
        make_new_window(window_key=event)

window.close()
