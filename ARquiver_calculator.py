"""A program to work with AR quiver and compute various objects.
This uses PySimpleGUI for GUI implementation.

The purpose of this program is to input AR quiver in several ways,
and calculate various objects from it.

Actual computation is achieved by `ARquiver.py`
and its class `TranslationQuiver`,
hence the main aim of this program is
to provide a GUI interface for `ARquiver.py`.

GitHub Repository:
https://github.com/haruhisa-enomoto/ARquiver
"""
from __future__ import annotations
import pickle
import re
import webbrowser

import PySimpleGUI as sg

from ARquiver import TranslationQuiver


# ----- Define classes `Vertex` and `Arrow` -----
class Vertex:
    def __init__(self, name: str, location: tuple[float, float]) -> None:
        self.name = name
        self.location = location

    def draw(self) -> None:
        """Draw `self` in our graph object.
        When this is called, two attributes are assigned:
        `self.circle` (int):
            the circle drawn in the canvas, represented by an element ID.
        `self.label` (int):
            the text label of `self.name` written in the canvas,
            represented by an element ID.
        """
        self.circle = graph.draw_circle(self.location, 30, fill_color="bisque",
                                        line_color="darkorange",
                                        line_width=2)
        self.label = graph.draw_text(self.name, self.location,
                                     font="Helvetica 15")

    def update_location(self) -> None:
        """Update `self.location`.
        This will be called if the vertex is dragged and moved.
        """
        self.location = location_of_fig(self.circle)  # type: ignore

    def delete(self) -> None:
        """Delete figure from our graph object.
        NOTE: This doesn't touch the global list `vertices`.
        """
        graph.delete_figure(self.circle)
        graph.delete_figure(self.label)


class Arrow:
    def __init__(self, source: Vertex, target: Vertex, tau: bool = False):
        """A class of arrows.

        Args:
            source (Vertex): arrow's source vertex.
            target (Vertex): arrow's target vertex.
            tau (bool, optional): Whether this is a translation arrow.
                Defaults to False.
        """
        self.source = source
        self.target = target
        self.is_tau = tau

    def draw(self) -> None:
        """Draw `self` in the canvas.
        """
        if self.is_tau:
            color, dash = "red", (10, 5)
        else:
            color, dash = "black", None
        if self.source != self.target:
            distance = ((self.source.location[0] - self.target.location[0])**2
                        + (self.source.location[1] - self.target.location[1])**2
                        )**0.5  # distance between source and target
            ratio = 30/distance
            head_loc = (self.source.location[0] * ratio
                        + self.target.location[0] * (1 - ratio),
                        self.source.location[1] * ratio
                        + self.target.location[1] * (1 - ratio))
            tail_loc = (self.source.location[0] * (1 - ratio)
                        + self.target.location[0] * ratio,
                        self.source.location[1] * (1 - ratio)
                        + self.target.location[1] * ratio)
            self.figure = graph.draw_line(tail_loc,
                                          head_loc,
                                          width=5, color=color)
            graph.TKCanvas.itemconfig(self.figure,  # type: ignore
                                      arrow="last",
                                      arrowshape=(15, 15, 8),
                                      dash=dash)
        else:  # Then this is a loop!
            circle_center = (self.source.location[0],
                             self.source.location[1] - 50)
            self.figure = graph.draw_circle(circle_center,
                                            50,
                                            line_width=5,
                                            line_color=color)
            graph.TKCanvas.itemconfig(self.figure, dash=dash)  # type: ignore
        graph.send_figure_to_back(self.figure)

    def delete(self) -> None:
        """Delete figure from our graph object.
        NOTE: This doesn't touch the global list `arrows`.
        """
        graph.delete_figure(self.figure)
        # graph.delete_figure(self.fig_tip)


# ----- Global lists -----

vertices: list[Vertex] = []
arrows: list[Arrow] = []  # `arrows` contains both usual arrows and tau arrows.

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

info_text = """
AR quiver calculator ver 0.2.0.

This program is written in Python, and uses PySimpleGUI.
Actually, the actual computation algorithm is written in another module
`ARquiver`, and what this program does is only to provide a framework to
input the translation quiver in GUI.
Source codes of this and `ARquiver` are available in GitHub.

Author: Haruhisa Enomoto
"""

ref_text = """
[Iy1] O. Iyama, tau-categories I: Ladders,
    Algebr. Represent. Theory 8 (2005), no. 3, 297–321.

[Iy2] O. Iyama, tau-categories II: Nakayama pairs and Rejective subcategories,
    Algebr. Represent. Theory 8 (2005), no. 4, 449–477.

[Iy3] O. Iyama, The relationship between homological properties
    and representation theoretic realization of artin algebras,
    Trans. Amer. Math. Soc. 357 (2005), no. 2, 709–734.

[INP] O. Iyama, H. Nakaoka, Y. Palu,
    Auslander-Reiten theory in extriangulated categories, arXiv:1805.03776.
"""

alg_text = """
--- dim Hom(X,Y) ---

Our method is based on the computation of so-called ladders for tau-categories in [Iy1, 7.2],
which gives an algorithm to compute the minimal projective presentation of J^n(-,Y) for given Y,
where J is the Jacobson radical.

--- Shift functor on triangulated category ---

If our category C is triangulated, then it has AR triangles since it is Hom-finite Krull-Schmidt and has only finitely many indecomposables.
Thus it has a Serre functor S. Then it is well-known that S is a composition of tau and shift.
Thus Hom(-, tau X[1]) = D Hom(X, -), hence Hom(-, X[1]) = D Hom(tau^{-1}X, -).
If we consider modules over C, then Hom(-, X[1]) has a simple top X[1],
thus by the above duality, we must have that X[1] is the socle of a projective module Hom(tau^{-1}X, -).
Therefore, we compute socle of Hom(tau^{-1}X, -) using radical layer.
"""

hom_text1 = """
This will calculate the dimension of Hom(X,Y) as a vector space
for two indecomposables X and Y in your AR quiver.
"""

hom_text2 = """
______________________________

We also compute the radical layer of Hom(-,Y) and Hom(X,-).
This is the successive quotient of the radical filtration
Hom(-,Y) > J(-,Y) > J^2(-,Y) > ...
where J is the Jacobson radical of C.
This shows the "module structure" or "composition series notation"
of these "modules" over our category.
See "Explanation" Tab for details and how it works.

NOTE: If the computation fails into infinite loop or doesn't terminate,
then "Ellipsis" appears at last.
"""

tri_text = """
In this tab, we assume that your category is a Hom-finite Krull-Schmidt triangulated category with shift functor Sigma.
Your quiver should be a stable translation quiver, that is, tau is defined for every vertex.

Ext^n(X, Y) is defined by Hom(X, Sigma^n Y) for an integer n.
"""

tri_ortho_text = """
We will list all objects M in your triangulated categories s.t. Ext^n(M, M) = 0 for a given n (several values possible).

(We use identify basic objects in your category with the list of vertices by taking direct sums.)

NOTE: 0 object corresponds to the empty list and counted!
______________________________
"""


# -----GUI Layout START-----

sg.theme('DarkAmber')

vtx_col = [[sg.Text('List of vertices:')],
           [sg.Listbox([], size=(30, 5), key='-VTX-LIST-')],
           [sg.Text('Add vertices (input vertices separeted by space)')],
           [sg.Input(key='-VTX-FORM-', size=(30, 1), do_not_clear=False),
            sg.Button("Add", key='-ADD-VTX-')],
           [sg.Text("Delete the one selected above"),
            sg.Button("Delete", key="-DEL-VTX-")]]

arrow_col = [[sg.Text('List of arrows:')],
             [sg.Listbox([], size=(30, 5), key='-ARROW-LIST-')],
             [sg.Text('Add arrows (input "1 2" to add arrow from 1 to 2,\n'
                      'and "1 2 3" to add two arrows 1->2->3)')],
             [sg.Input(key='-ARROW-FORM-', size=(30, 1), do_not_clear=False),
              sg.Button("Add", key='-ADD-ARROW-')],
             [sg.Text("Delete the one selected above"),
              sg.Button("Delete", key="-DEL-ARROW-")]]

tau_col = [[sg.Text('List of AR translations:')],
           [sg.Listbox([], size=(30, 5), key='-TAU-LIST-')],
           [sg.Text('Add translation\n'
                    '(input "1 2" if tau(1) = 2,'
                    '"1 2 3" for tau(1) = 2, tau(2) = 3)')],
           [sg.Input(key='-TAU-FORM-', size=(30, 1), do_not_clear=False),
            sg.Button("Add", key='-ADD-TAU-')],
           [sg.Text("Delete the one selected above"),
            sg.Button("Delete", key="-DEL-TAU-")]]

col = [[sg.T('Choose operations (just click for add vertices)')],
       [sg.R('Draw a usual arrow', 1, default=True, key='-ARROW-')],
       [sg.R('Draw a translation arrow = tau', 1, key='-TAU-')],
       [sg.R('Delete item', 1, key='-ERASE-')],
       [sg.R('Move', 1, key='-MOVE-')],
       [sg.R("Move All", 1, key="-MOVEALL-")],
       [sg.Button('Clear')]]

size = (60, 40)
# initial size of the canvas. Small value for small environments.
bottom_right_corner = (2*size[0], 2*size[1])
# We use the following coordinate system.
# - The top left corner is (0,0)
# - The "initial" bottom right corner is `bottom_right_corner`
# Although the Canvas extends in x and y directions,
# it seems that the initial bottom right corner is remembered,
# and the coordinate does not changes.

input_layout = [[sg.Col(vtx_col), sg.Col(arrow_col), sg.Col(tau_col)],
                [sg.Graph(canvas_size=size,
                          graph_bottom_left=(0, bottom_right_corner[1]),
                          graph_top_right=(bottom_right_corner[0], 0),
                          key="-GRAPH-",
                          enable_events=True, background_color='white',
                          drag_submits=True, float_values=True,
                          expand_x=True, expand_y=True),
                 sg.Col(col)],
                [sg.Text("To use Calculation tab, push the right button:"),
                 sg.Button("Complete!")]]

hom_input_col = [[sg.Text("X = "), sg.Combo([], size=(5, 1), key="-HOM-X-")],
                 [sg.Text("Y = "), sg.Combo([], size=(5, 1), key="-HOM-Y-")]]

hom_layout = [[sg.Text(hom_text1)],
              [sg.Text("Let's compute dim_k Hom(X,Y). Choose X and Y.")],
              [sg.Col(hom_input_col),
               sg.Button("Calculate!", key="-HOM-CAL-"),
               sg.Text("dim_k Hom(X,Y) = "),
               sg.Text("", key="-HOM-OUT-")],
              [sg.Text(hom_text2)],
              [sg.Text("The radical series of Hom(X,-) is"),
               sg.Listbox([], size=(30, 5), expand_x=True, key="-HOM-COV-"),
               sg.Text("The radical series of Hom(-,Y) is"),
               sg.Listbox([], size=(30, 5), expand_x=True, key="-HOM-CONT-")]
              ]

tri_shift_layout = [[sg.Text("Calculations on the shift functor Sigma.")],
                    [sg.Text("1. Calculate Sigma^n (X)")],
                    [sg.Text("X = "),
                     sg.Combo([], size=(5, 1), key="-TRI-SHIFT-"),
                     sg.Text("n = (default 1)"),
                     sg.Input(size=(5, 1), key="-TRI-SHIFT-DEG-"),
                     sg.Button("Calculate!", key="-TRI-SHIFT-CAL-"),
                     sg.Text("Sigma^n (X) = "),
                     sg.Text("", key="-TRI-SHIFT-OUT-")],
                    [sg.Text("_"*30)],
                    [sg.Text("2. Calculation of Serre functor.")],
                    [sg.Text("Serre functor is well-known to be"
                             "the composition of tau and shift.")],
                    [sg.Text("X = "),
                     sg.Combo([], size=(5, 1), key="-TRI-SER-"),
                     sg.Button("Calculate!", key="-TRI-SER-CAL-"),
                     sg.Text("Serre(X) = "),
                     sg.Text("", key="-TRI-SER-OUT-")],
                    [sg.Text("_"*30)],
                    [sg.Text("3. Objectwise period of shift functor")],
                    [sg.Text("Compute the period of the action of Sigma"
                             " on objects.")],
                    [sg.Text("NOTE: This could be different from"
                             " the period of the functor Sigma,"
                             " since we don't consider the action on Hom.")],
                    [sg.Button("Calculate!", key="-TRI-PER-CAL-")],
                    [sg.Text("Period (on objects) is "),
                     sg.Text("", key="-TRI-PER-OUT-")]]


tri_ortho_layout = [[sg.Text(tri_ortho_text)],
                    [sg.Text("Input n s.t. you want Ext^n to vanish."
                             "(default: 1)\n"
                             "Input like '1 2 3' if you want Ext^1, "
                             "Ext^2 and Ext^3 to vanish."),
                     sg.Input(size=(30, 1), key="-TRI-DEG-"),
                     sg.Button("Calculate!", key="-TRI-ORTHO-CAL-")],
                    [sg.Text("Here are maximal objects with Ext^n vanishes:"),
                     sg.Listbox([], size=(30, 5), key="-TRI-ORTHO-OUT1-")],
                    [sg.Text("The number of such objects is"),
                     sg.Text("", key="-TRI-ORTHO-NUM1-")],
                    [sg.Text("_"*30)],
                    [sg.Text("Without the maximality condition, "
                             "basic orthogonal objects are:"),
                     sg.Listbox([], size=(30, 5), key="-TRI-ORTHO-OUT2-")],
                    [sg.Text("The number of such objects is"),
                     sg.Text("", key="-TRI-ORTHO-NUM2-")]
                    ]

tri_layout = [[sg.Text(tri_text)],
              [sg.TabGroup(
                  [[sg.Tab("Calculation of shift", tri_shift_layout),
                    sg.Tab("Calculation of Ext-orthogonals",
                           tri_ortho_layout)]],
                  expand_x=True, expand_y=True
              )]]

menu_def = [['&File', ['&Open', '&Save', "Save &As...", '---',
                       '&Import from String Applet',
                       '&Export', ['Export the translation quiver data',
                                   'Export the tex (not implemented!)'],
                       '---', 'E&xit', ]],
            ['Help', ['About this program', '---',
                      'Assumptions', 'How it works', '---', 'References']]]

layout = [[sg.Menu(menu_def)],
          [sg.TabGroup([[sg.Tab("Input your AR quiver", input_layout),
                         sg.Tab("Calculation of Hom", hom_layout),
                         sg.Tab("Triangulated categories", tri_layout)
                         ]],
                       expand_x=True, expand_y=True)]]

window_title = "AR quiver calculator ver. 0.2.0"
window = sg.Window(window_title, layout,
                   resizable=True, finalize=True,
                   enable_close_attempted_event=True)
window.maximize()

graph: sg.Graph = window["-GRAPH-"]  # type: ignore

# -----GUI Layout END-----

dragging = False
drawing_arrow = False
vertex_keys = ["-HOM-X-", "-HOM-Y-", "-TRI-SHIFT-", "-TRI-SER-"]
quiver = None  # The created TranslationQuiver object will be assigned.
file_path = None
changed = None

# -----Some functions to draw AR quivers-----


def draw_arrow(source: Vertex, target: Vertex, tau: bool = False) -> None:
    """
    Draw an arrow from `source` to `target`, construct an instance of `Arrow`,
    and add it to `arrows`.
    """
    arrow = Arrow(source, target, tau)
    arrow.draw()
    arrows.append(arrow)


def draw_vertex(name: str, location: tuple[float, float]) -> None:
    """
    Draw a vertex in position, construct an instance of Vertex,
    and add it to `vertices`.
    """
    vertex = Vertex(name, location)
    vertex.draw()
    vertices.append(vertex)


def delete_vtx(vertex: Vertex) -> None:
    """
    Delete `vertex` and its related arrows from the canvas,
    and also remove them from `vertices` and `arrows`.
    """
    global drawing_arrow
    vertex.delete()
    if drawing_arrow:
        graph.TKCanvas.itemconfig(source_vtx.circle, fill="bisque")  # type: ignore
        drawing_arrow = False
    vertices.remove(vertex)
    search_arrow_con = [a for a in arrows if vertex in (a.source, a.target)]
    for arrow in search_arrow_con:
        arrow.delete()
        arrows.remove(arrow)


def location_of_fig(figure: int) -> tuple[float, float]:
    """
    Return the cooridnate (x,y) of the center of `figure`.
    """
    (x1, y1), (x2, y2) = graph.get_bounding_box(figure)
    return ((x1 + x2)/2, (y1 + y2)/2)  # type: ignore


def add_vtx_from_form(lst: list[str]) -> None:
    """
    Add vertices from input form
    and draw the corresponding vertex in the figure.
    """
    names = [v.name for v in vertices]
    lst = sorted(list(set(names + lst) - set(names)))
    # Only add new vertices

    size: tuple[float, float] = graph.get_size()  # type: ignore

    i = 1
    for vtx in lst:
        N = len(lst) + 1
        draw_vertex(vtx, (i/N * 2 * size[0], size[1]))
        i = i+1
    update_info()


def update_info() -> None:
    """
    Update the displayed information.
    """
    vertices_list = sorted([vertex.name for vertex in vertices])
    arrows_list = sorted([str(ar.source.name) + "---->" + str(ar.target.name)
                          for ar in arrows if not ar.is_tau])
    tau_list = sorted([str(ar.source.name) + "--tau-->" + str(ar.target.name)
                       for ar in arrows if ar.is_tau])
    window['-VTX-LIST-'].update(values=vertices_list)
    window['-ARROW-LIST-'].update(values=arrows_list)
    window['-TAU-LIST-'].update(values=tau_list)


def make_new_window(window_key: str) -> None:
    """
    Make the new window (modal) for info, references, etc, and wait for events.
    """
    if window_key == "About this program":
        layout = [[sg.Text(info_text)],
                  [sg.Button("Author's website", key="-WEB-"),
                   sg.Button('GitHub'), sg.OK()]]

    elif window_key == "References":
        layout = [[sg.Text(ref_text)],
                  [sg.OK()]]

    elif window_key == "How it works":
        layout = [[sg.Text(alg_text)],
                  [sg.OK()]]

    elif window_key == "Assumptions":
        layout = [[sg.Text(assump_text)],
                  [sg.OK()]]

    new_window = sg.Window(window_key, layout, modal=True)
    while True:
        event, _ = new_window.read()  # type: ignore
        if event in (sg.WIN_CLOSED, "OK"):
            break
        elif event == "-WEB-":
            webbrowser.open_new("https://haruhisa-enomoto.github.io/")
        elif event == "GitHub":
            webbrowser.open_new("https://github.com/haruhisa-enomoto/ARquiver")

    new_window.close()


# -----Event Loop-----
while True:
    event: str
    values: dict
    event, values = window.read()  # type: ignore
    # print(event, values, "\n____")

    if event == sg.WIN_CLOSE_ATTEMPTED_EVENT and not changed:
        break

    elif (event == sg.WIN_CLOSE_ATTEMPTED_EVENT
          and sg.popup_yes_no("Are you sure to discard changes?",
                              title="Warning") == "Yes"):
        break

    elif event == 'Clear':
        changed = True
        graph.erase()
        vertices, arrows = [], []
        update_info()

    elif event == '-ADD-VTX-':
        changed = True
        add_vtx_from_form(values['-VTX-FORM-'].split())
        update_info()

    elif event == '-ADD-ARROW-':
        changed = True
        data = values["-ARROW-FORM-"].split()
        if len(data) < 2:
            sg.popup("Please input like '1 2' for 1->2.",
                     title="Error")
        else:
            # First add new vertices if needed
            names = [v.name for v in vertices]
            new_names = sorted(list(set([x for x in data if x not in names])))
            add_vtx_from_form(new_names)
            for i in range(len(data)-1):
                source_name, target_name = data[i:i+2]
                source = [v for v in vertices if v.name == source_name][0]
                target = [v for v in vertices if v.name == target_name][0]
                draw_arrow(source, target)
            update_info()

    elif event == '-ADD-TAU-':
        changed = True
        data = values["-TAU-FORM-"].split()
        if len(data) < 2:
            sg.popup("Please input like '1 2' for tau(1)=2.",
                     title="Error")
        names = [v.name for v in vertices]
        new_names = sorted(list(set([x for x in data if x not in names])))
        add_vtx_from_form(new_names)
        for i in range(len(data)-1):
            source_name, target_name = data[i:i+2]
            source = [v for v in vertices if v.name == source_name][0]
            target = [v for v in vertices if v.name == target_name][0]
            draw_arrow(source, target, tau=True)
        update_info()

    elif event == "-DEL-VTX-":
        if not values["-VTX-LIST-"]:
            sg.popup("Please select a vertex from the list!",
                     title="Error")
        else:
            changed = True
            vertex_name = values["-VTX-LIST-"][0]
            vertex = [v for v in vertices if v.name == vertex_name][0]
            delete_vtx(vertex)
            update_info()

    elif event == "-DEL-ARROW-":
        if not values["-ARROW-LIST-"]:
            sg.popup("Please select an arrow from the list!",
                     title="Error")
        else:
            changed = True
            s_name, t_name = values["-ARROW-LIST-"][0].split("---->")
            arrow = [ar for ar in arrows
                     if ar.source.name == s_name
                     and ar.target.name == t_name][0]
            arrow.delete()
            arrows.remove(arrow)
            update_info()

    elif event == "-DEL-TAU-":
        if not values["-TAU-LIST-"]:
            sg.popup("Please select an arrow from the list!",
                     title="Error")
        else:
            changed = True
            s_name, t_name = values["-TAU-LIST-"][0].split("--tau-->")
            arrow = [ar for ar in arrows
                     if ar.source.name == s_name
                     and ar.target.name == t_name][0]
            arrow.delete()
            arrows.remove(arrow)
            update_info()

    elif event == "-GRAPH-":
        x: float
        y: float
        x, y = values["-GRAPH-"]
        if not dragging:
            dragging = True
            drag_figures = graph.get_figures_at_location((x, y))
            last_xy = x, y
            first_time = True
        else:
            first_time = False
        delta_x, delta_y = x - last_xy[0], y - last_xy[1]
        last_xy = x, y

        if ((values["-ARROW-"] or values["-TAU-"])
           and not drag_figures and first_time):
            # Then we add a vertex.
            # First decide the numbering of the vertices,
            # which is the smallest unused number.
            changed = True
            number: int = 1

            while True:
                if str(number) not in [v.name for v in vertices]:
                    break
                number = number + 1
            draw_vertex(str(number), (x, y))
            update_info()

        elif ((values["-ARROW-"] or values["-TAU-"])
              and drag_figures and first_time):
            # Then draw an arrow.
            is_tau: bool = values["-TAU-"]
            figure: int = drag_figures[-1]
            search = [v for v in vertices if figure in (v.circle, v.label)]
            # Search a vertex which is clicked.
            if search:
                vertex = search[0]
                if not drawing_arrow:
                    # Then this vertex is selected as a source.
                    source_vtx = vertex
                    drawing_arrow = True
                    # Change color!
                    graph.TKCanvas.itemconfig(
                        source_vtx.circle, fill="orange")  # type: ignore
                else:
                    changed = True
                    # Then this vertex is a target, and we will draw an arrow.
                    draw_arrow(source_vtx, vertex, is_tau)
                    graph.TKCanvas.itemconfig(
                        source_vtx.circle, fill="bisque")  # type: ignore
                    drawing_arrow = False
                    update_info()

        elif values['-ERASE-'] and drag_figures:
            figure = drag_figures[-1]
            search_vtx = [v for v in vertices if figure in (v.circle, v.label)]
            search_arrow = [a for a in arrows if figure == a.figure]
            if search_vtx:
                changed = True
                vertex = search_vtx[0]
                delete_vtx(vertex)
            elif search_arrow:
                changed = True
                for arrow in search_arrow:
                    arrow.delete()
                    arrows.remove(arrow)
            update_info()

        elif drag_figures:
            # Then move!
            figure = drag_figures[-1]
            search = [v for v in vertices if figure in (v.circle, v.label)]
            # Search a dragged vertex.
            if search:
                changed = True
                vertex = search[0]
                graph.move_figure(vertex.circle, delta_x, delta_y)
                graph.move_figure(vertex.label, delta_x, delta_y)
                vertex.update_location()
                search_arrow = [a for a in arrows
                                if vertex in (a.source, a.target)]
                for arrow in search_arrow:
                    arrow.delete()
                    arrows.remove(arrow)
                    draw_arrow(arrow.source, arrow.target, arrow.is_tau)
                graph.update()
        elif values['-MOVEALL-']:
            changed = True
            graph.move(delta_x, delta_y)
            for vertex in vertices:
                vertex.update_location()

    elif event.endswith('+UP'):  # The drawing has ended because mouse up
        dragging = False

    elif event == "Complete!":
        # Construct an instance of `TranslationQuiver`.
        # Vertices are represented by their name.

        # First construct a dictionary tau.
        tau_domain = [ar.source.name for ar in arrows if ar.is_tau]
        tau: dict[str, str] = dict()
        for v in tau_domain:
            tau_vs = [ar.target.name for ar in arrows
                      if ar.source.name == v and ar.is_tau]
            if len(tau_vs) != 1:
                sg.popup("Some tau-arrows have the same codomain!",
                         title="Error")
            tau[v] = tau_vs[0]
        arrow_list = [(ar.source.name, ar.target.name)
                      for ar in arrows if not ar.is_tau]
        # Try to construct a TranslationQuiver,
        # and then enables and modify "Calculation of Hom" tab.
        try:
            quiver = TranslationQuiver(tuple([v.name for v in vertices]),
                                       tuple(arrow_list),
                                       tau)
            sg.popup("Your AR quiver have been successfully inputted!",
                     title="Success!")
            names = [v.name for v in vertices]
            for key in vertex_keys:
                window[key].update(values=names)
        except ValueError as e:
            sg.popup(e, title="Error")

    # --- Event on Save and open ---
    elif event == "Save" and file_path:
        with open(file_path, "wb") as f:
            pickle.dump((vertices, arrows), f)
        changed = False

    elif (event == "Save" and not file_path) or event == "Save As...":
        file_path = sg.popup_get_file(
            "Enter a filename.",
            default_extension="pickle",
            file_types=[("Pickle file", "*.pickle"), ('ALL Files', '*.*')],
            save_as=True,
            no_window=True)
        if file_path:
            try:
                with open(file_path, "wb") as f:
                    pickle.dump((vertices, arrows), f)
                window.TKroot.title(file_path
                                    + " - " + window_title)
                changed = False
            except Exception as e:
                sg.popup(e, title="Error")

    elif event == "Open":
        sure = "Yes"
        if changed:
            sure = sg.popup_yes_no("Are you sure to discard changes?",
                                   title="Warning")
        if sure == "Yes":
            file_path = sg.popup_get_file(
                "Choose saved data (Current state will be discarded!)",
                title="Open",
                file_types=[("Pickle file", "*.pickle"), ('ALL Files', '*.*')],
                no_window=True)
            if file_path:
                try:
                    with open(file_path, "rb") as f:
                        vertices, arrows = pickle.load(f)
                        graph.erase()
                        for v in vertices:
                            v.draw()
                        for ar in arrows:
                            ar.draw()
                        window.TKroot.title(
                            file_path + " - " + window_title)
                        changed = False
                except Exception as e:
                    sg.popup(e, title="Error")
                update_info()

    elif event == "Export the translation quiver data":
        if not quiver:
            sg.popup("Please click 'Complete!' button.",
                     title="Error")
        else:
            file_path = sg.popup_get_file(
                "The created object of a class `TranslationQuiver` "
                "will be saved. Enter a filename.",
                default_extension="pickle",
                file_types=[("Pickle file", "*.pickle")],
                save_as=True,
                no_window=True)
            if file_path:
                try:
                    with open(file_path, "wb") as f:
                        pickle.dump(quiver, f)
                except Exception as e:
                    sg.popup(e)

    # --- Event concerning calculations ---

    elif event == "-HOM-CAL-":
        if not quiver:
            sg.popup("Please click 'Complete!' button.",
                     title="Error")
        else:
            names = [v.name for v in vertices]
            X, Y = values["-HOM-X-"], values["-HOM-Y-"]
            try:
                dim = quiver.hom(X, Y)
                window["-HOM-OUT-"].update(dim)
            except ValueError as e:
                sg.popup(e, title="Error")
            try:
                hom_X_layer = quiver.radical_layer(X, contravariant=False)
                hom_Y_layer = quiver.radical_layer(Y)
                window["-HOM-COV-"].update(values=hom_X_layer)
                window["-HOM-CONT-"].update(values=hom_Y_layer)
            except ValueError as e:
                sg.popup(e, title="Error")

    elif event == "-TRI-SHIFT-CAL-":
        if not quiver:
            sg.popup("Please click 'Complete!' button.",
                     title="Error")
        else:
            X = values["-TRI-SHIFT-"]
            degree = values["-TRI-SHIFT-DEG-"]
            if degree:
                degree = int(degree)
            else:
                degree = 1
            try:
                shift_X = quiver.shift(X, degree)
                window["-TRI-SHIFT-OUT-"].update(shift_X)
            except ValueError as e:
                sg.popup(e, title="Error")

    elif event == "-TRI-SER-CAL-":
        if not quiver:
            sg.popup("Please click 'Complete!' button.",
                     title="Error")
        else:
            X = values["-TRI-SER-"]
            try:
                result = quiver.Serre_functor(X)
                window["-TRI-SER-OUT-"].update(result)
            except ValueError as e:
                sg.popup(e, title="Error")

    elif event == "-TRI-PER-CAL-":
        if not quiver:
            sg.popup("Please click 'Complete!' button.",
                     title="Error")
        else:
            try:
                period = quiver.period()
                window["-TRI-PER-OUT-"].update(period)
            except ValueError as e:
                sg.popup(e, title="Error")

    elif event == "-TRI-ORTHO-CAL-":
        if not quiver:
            sg.popup("Please click 'Complete!' button.",
                     title="Error")
        else:
            try:
                degrees = [int(n) for n in values["-TRI-DEG-"].split()]
                if not degrees:
                    degrees = [1]
                result1 = quiver.maximal_ext_orthogonals(degrees)
                result2 = quiver.ext_orthogonals(degrees)
                result1.sort(key=lambda lst: (len(lst), lst))
                result2.sort(key=lambda lst: (len(lst), lst))
                window["-TRI-ORTHO-OUT1-"].update(values=result1)
                window["-TRI-ORTHO-NUM1-"].update(len(result1))
                window["-TRI-ORTHO-OUT2-"].update(values=result2)
                window["-TRI-ORTHO-NUM2-"].update(len(result2))
            except Exception as e:
                sg.popup(e, title="Error")

    elif event == "Import from String Applet":
        file_path = sg.popup_get_file(
            "Enter your tex file exported from String Applet",
            file_types=[("LaTeX file", "*.tex"), ('ALL Files', '*.*')],
            no_window=True
            )
        if file_path:
            with open(file_path, "r", encoding='utf-8') as f:
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
                    match = re.search(r'node \((.*)\) at', line)
                    if match:
                        vtx_name = match.group(1)
                        location_str = re.search(r'at \((.*)\)', line).group(1)
                        x_str, y_str = location_str.split(",")
                        location = (3 * float(x_str), 3 * float(y_str))
                        loaded_vertices.append((vtx_name, location))
                elif scope_count == 2:
                    match = re.findall(r'\((.+?)\)', line)
                    tau_search = re.search(r'dotted', line)
                    is_tau: bool = False
                    if match:
                        source, target = match[0], match[1]
                        if tau_search:
                            is_tau = True
                        loaded_arrows.append((source, target, is_tau))
                else:
                    break
            vertices, arrows = [], []
            # Normalize cooridnate so that the smallest values of x and y
            # are (30, 30).
            min_x = min([x for _, (x, _) in loaded_vertices]) - 30
            min_y = min([y for _, (_, y) in loaded_vertices]) - 30
            loaded_vertices = [(name, (x - min_x, y - min_y))
                               for name, (x, y) in loaded_vertices]
            graph.erase()
            for vtx_name, location in loaded_vertices:
                draw_vertex(vtx_name, location)
            # add_vtx_from_form(loaded_vertices)
            for source_name, target_name, is_tau in loaded_arrows:
                source = [v for v in vertices if v.name == source_name][0]
                target = [v for v in vertices if v.name == target_name][0]
                draw_arrow(source, target, is_tau)
            update_info()

    # --- Event making new window ---

    elif event in ("References", "About this program",
                   "How it works", "Assumptions"):
        make_new_window(window_key=event)

window.close()
