import PySimpleGUI as sg

# Colors for vertices
usual_color, border_color, select_color = "gray90", "gray20", "lightsalmon"
cat_color1, cat_color2 = "CadetBlue1", "light pink"

# ----- Classes `Vertex` and `Arrow` -----


class Vertex:
    """A class for vertices.

    Attributes:
        `name` (str): name
        `location`: coordinate in our main graph
        `circle_id` (dict[str, int]): dictionary of ids of circle objects
            in our graphs.
        `label_id` (dict[str, int]): dictionary of ids of label objects
            in our graphs.
        `graphdict` (dict[str, sg.Graph]): dictionary of ids of sg.Graph objects.
            It needs to contain at least one entry with key "main".
    """

    def __init__(
        self, name: str, location: tuple[float, float], graphdict: dict[str, sg.Graph]
    ) -> None:
        self.name = name
        self.location = location
        self.circle_id: dict[str, int] = {}
        self.label_id: dict[str, int] = {}
        self.selected: bool = False
        self.str_to_graph: dict[str, sg.Graph] = (
            graphdict if "main" in graphdict else {"main": None, **graphdict}
        )  # temporary resolution... may need better handling

    def __str__(self):
        return self.name

    def __int__(self):  # Used for sorting
        try:
            return int(self.name)
        except ValueError:
            return 0

    def __lt__(self, other):
        return int(self) < int(other)

    def __eq__(self, other):
        if not isinstance(other, Vertex):
            return NotImplemented
        return self.name == other.name

    def toggle(self, graph_name: str = "main"):
        self.selected = not self.selected
        self.draw(graph_name)

    def select(self, graph_name: str = "main"):
        if not self.selected:
            self.toggle(graph_name)

    def unselect(self, graph_name: str = "main"):
        if self.selected:
            self.toggle(graph_name)

    def draw(self, graph_name: str = "main"):
        """Draw `self` in our graph with name `graph_name`."""
        if not hasattr(self, "circle_id"):  # For backward compatibility
            self.circle_id = {}
            self.label_id = {}
        g = self.str_to_graph[graph_name]
        if graph_name in self.circle_id:
            g.delete_figure(self.circle_id[graph_name])
            g.delete_figure(self.label_id[graph_name])
        circ = g.draw_circle(
            self.location,
            15,
            fill_color=select_color if self.selected else usual_color,
            line_color=border_color,
            line_width=2,
        )
        label = g.draw_text(self.name, self.location, font="Helvetica 15")
        self.circle_id[graph_name], self.label_id[graph_name] = circ, label

    def update_location(self) -> None:
        """Update `self.location` accorindg to the current location
        in our main graph.
        """
        (x1, y1), (x2, y2) = self.str_to_graph["main"].get_bounding_box(
            self.circle_id["main"]
        )
        self.location = ((x1 + x2) / 2, (y1 + y2) / 2)

    def delete(self, graph_name: str = "main") -> None:
        """Delete figure from our graph object with name `graph_name`.
        NOTE: This doesn't touch the global list `vertices`.
        """
        self.str_to_graph["main"].delete_figure(self.circle_id[graph_name])
        self.str_to_graph["main"].delete_figure(self.label_id[graph_name])


class Arrow:
    """A class for arrows.
    This both contains usual arrows and AR-translation arrows.

    Attributes:
        source (Vertex): arrow's source vertex.
        target (Vertex): arrow's target vertex.
        tau (bool, optional): Whether this is a translation arrow.
            Defaults to False.
        figure_id (dict[str, int]): dictionary of ids of the arrow
            in our graphs.
    """

    def __init__(
        self,
        source: Vertex,
        target: Vertex,
        graphdict: dict[str, sg.Graph],
        tau: bool = False,
    ):
        self.source = source
        self.target = target
        self.is_tau = tau
        self.figure_id: dict[str, int] = {}
        self.str_to_graph: dict[str, sg.Graph] = (
            graphdict if "main" in graphdict else {"main": None, **graphdict}
        )  # temporary resolution... may need better handling

    def __str__(self):
        if not self.is_tau:
            return self.source.name + "---->" + self.target.name
        else:
            return self.source.name + "--tau-->" + self.target.name

    def __lt__(self, other):  # For sorting.
        return (self.source, self.target) < (other.source, other.target)

    def draw(self, graph_name: str = "main") -> None:
        """Draw `self` in our graph with name `graph_name`."""
        if not hasattr(self, "figure_id"):
            self.figure_id = {}
        g = self.str_to_graph[graph_name]
        if graph_name in self.figure_id:
            g.delete_figure(self.figure_id[graph_name])
        if self.is_tau:
            color, dash = "red3", (10, 5)
        else:
            color, dash = "black", None
        if self.source != self.target:
            distance = (
                (self.source.location[0] - self.target.location[0]) ** 2
                + (self.source.location[1] - self.target.location[1]) ** 2
            ) ** 0.5  # distance between source and target
            ratio = 15 / distance
            head_loc = (
                self.source.location[0] * ratio + self.target.location[0] * (1 - ratio),
                self.source.location[1] * ratio + self.target.location[1] * (1 - ratio),
            )
            tail_loc = (
                self.source.location[0] * (1 - ratio) + self.target.location[0] * ratio,
                self.source.location[1] * (1 - ratio) + self.target.location[1] * ratio,
            )
            id = g.draw_line(tail_loc, head_loc, width=3, color=color)
            g.tk_canvas.itemconfig(id, arrow="last", arrowshape=(8, 15, 8), dash=dash)
        else:  # Then this is a loop!
            circle_center = (self.source.location[0], self.source.location[1] - 25)
            id = g.draw_circle(circle_center, 25, line_width=3, line_color=color)
            g.tk_canvas.itemconfig(id, dash=dash)
        g.send_figure_to_back(id)
        self.figure_id[graph_name] = id

    def delete(self, graph_name: str = "main") -> None:
        """Delete figure from our graph object with name `graph_name`.
        NOTE: This doesn't touch the global list `arrows`.
        """
        self.str_to_graph["main"].delete_figure(self.figure_id[graph_name])
