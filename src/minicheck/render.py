"""Render a counterexample as something a human can look at.

The counterexample is the product. Until now it rendered as a table of field assignments, which is
the least legible form of the most valuable thing the checker produces. A reviewer looking at a
failed CI job wants to *see* the interleaving that breaks the protocol.

Three formats, chosen for where people already are:

``mermaid``   GitHub renders it natively in PRs, issues and Markdown files, so a CI comment can show
              the diagram inline with no image hosting.
``dot``       Graphviz, for papers and anywhere you want real layout control.
``svg``       Self-contained, no toolchain, no JavaScript — openable in a browser or embeddable.

Every renderer draws the *reachable graph* with the counterexample path highlighted, so the trace is
shown in the context of the states it passed by. Graphs above `max_nodes` are refused rather than
emitted as an unreadable hairball — a diagram nobody can read is not a diagram.
"""

from __future__ import annotations

from .verdict import Verdict

__all__ = ["to_mermaid", "to_dot", "to_svg", "RenderTooLarge", "DEFAULT_MAX_NODES"]

#: Above this many states a diagram stops being informative, so it is refused.
DEFAULT_MAX_NODES = 60


class RenderTooLarge(ValueError):
    """The reachable graph is too big to draw legibly.

    Raised rather than emitting a diagram nobody can read. The message says how to narrow it.
    """


def _fmt(state: dict) -> str:
    return ", ".join(f"{k}={v}" for k, v in state.items())


def _collect(model, max_nodes: int):
    """Reachable states and edges in BFS order, plus whether the walk finished.

    Returns ``(order, edges, complete)``. ``complete`` is False when the model refused to expand —
    an unbounded integer field raising `IntBoundExceeded` mid-walk. That is not a rendering error
    and must not crash the caller: a partial picture of a machine whose space is not finite is
    still useful, as long as the diagram *says* it is partial. Silently drawing it as though it
    were the whole graph would be the visual form of a truncated proof.

    Exceeding ``max_nodes`` is different and still refuses outright — that is a legibility limit,
    not a property of the model.
    """
    from collections import deque

    from ._core import SearchIncomplete

    order = [model.initial]
    seen = {model.initial}
    edges = []
    complete = True
    q = deque([model.initial])
    try:
        while q:
            s = q.popleft()
            for label, ns in model.transitions(s):
                edges.append((s, label, ns))
                if ns not in seen:
                    if len(seen) >= max_nodes:
                        raise RenderTooLarge(
                            f"the reachable graph exceeds {max_nodes} states, which does not render "
                            f"legibly. Raise max_nodes if you really want it, or narrow the model — a "
                            f"diagram is for understanding one counterexample, not surveying a space."
                        )
                    seen.add(ns)
                    order.append(ns)
                    q.append(ns)
    except SearchIncomplete:
        complete = False
    return order, edges, complete


def _trace_states(counterexample, fields) -> list:
    """The counterexample as state tuples, for highlighting."""
    if not counterexample:
        return []
    return [tuple(step["state"][f] for f in fields) for step in counterexample]


def to_mermaid(model, counterexample=None, *, verdict=None, max_nodes: int = DEFAULT_MAX_NODES) -> str:
    """A Mermaid `stateDiagram-v2`. Renders natively in GitHub Markdown.

    The counterexample path is drawn in red and its steps numbered, so the order is unambiguous —
    a highlighted subgraph without ordering leaves the reader to guess which edge came first.
    """
    order, edges, complete = _collect(model, max_nodes)
    ids = {s: f"S{i}" for i, s in enumerate(order)}
    path = _trace_states(counterexample, model.fields)

    out = ["stateDiagram-v2"]
    if verdict is not None:
        out.append(f"    %% verdict: {Verdict(verdict).value}")
    if not complete:
        out.append("    %% PARTIAL: the state space is not finite under this bound; more states exist")
    out.append(f"    [*] --> {ids[model.initial]}")
    for s in order:
        out.append(f"    {ids[s]} : {_fmt(model.d(s))}")

    step = {}
    for i in range(len(path) - 1):
        step[(path[i], path[i + 1])] = i + 1
    for s, label, ns in edges:
        if ns not in ids:
            continue
        n = step.get((s, ns))
        text = f"{n}. {label}" if n else label
        out.append(f"    {ids[s]} --> {ids[ns]} : {text}")
    for s in path:
        if s in ids:
            out.append(f"    class {ids[s]} cex")
    if path:
        out.append("    classDef cex fill:#fdd,stroke:#c00,stroke-width:2px")
    return "\n".join(out)


def to_dot(model, counterexample=None, *, verdict=None, max_nodes: int = DEFAULT_MAX_NODES) -> str:
    """Graphviz DOT. `dot -Tpng out.dot -o out.png`."""
    order, edges, complete = _collect(model, max_nodes)
    ids = {s: f"s{i}" for i, s in enumerate(order)}
    path = _trace_states(counterexample, model.fields)
    on_path = set(path)
    step = {(path[i], path[i + 1]): i + 1 for i in range(len(path) - 1)}

    out = ["digraph counterexample {", "  rankdir=LR;", '  node [shape=box, fontname="monospace"];']
    if verdict is not None:
        label = f"verdict: {Verdict(verdict).value}"
        if not complete:
            label += "  (PARTIAL: more states exist beyond the bound)"
        out.append(f'  label="{label}"; labelloc=t;')
    elif not complete:
        out.append('  label="PARTIAL: more states exist beyond the bound"; labelloc=t;')
    for s in order:
        style = ' style=filled fillcolor="#ffdddd" color="#cc0000"' if s in on_path else ""
        out.append(f'  {ids[s]} [label="{_fmt(model.d(s))}"{style}];')
    for s, label, ns in edges:
        if ns not in ids:
            continue
        n = step.get((s, ns))
        if n:
            out.append(f'  {ids[s]} -> {ids[ns]} [label="{n}. {label}" color="#cc0000" penwidth=2];')
        else:
            out.append(f'  {ids[s]} -> {ids[ns]} [label="{label}" color="#999999"];')
    out.append("}")
    return "\n".join(out)


def to_svg(model, counterexample=None, *, verdict=None, max_nodes: int = DEFAULT_MAX_NODES) -> str:
    """A self-contained SVG of the counterexample path, laid out left to right.

    Deliberately draws ONLY the trace, not the whole graph: without a layout engine there is no
    honest way to place an arbitrary graph, and a bad layout is worse than a simple one. For the
    full reachable graph use `to_dot` and run Graphviz.
    """
    path = _trace_states(counterexample, model.fields)
    if not path:
        raise ValueError("to_svg needs a counterexample; there is no trace to draw without one")
    if len(path) > max_nodes:
        raise RenderTooLarge(f"trace has {len(path)} steps, above max_nodes={max_nodes}")

    labels = [step["label"] or "initial" for step in counterexample]
    bw, bh, gap, pad = 190, 54, 46, 24
    w = pad * 2 + len(path) * bw + (len(path) - 1) * gap
    h = pad * 2 + bh + 54

    esc = lambda t: str(t).replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")  # noqa: E731
    out = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{w}" height="{h}" viewBox="0 0 {w} {h}">',
        "<defs><marker id='a' markerWidth='9' markerHeight='7' refX='9' refY='3.5' orient='auto'>"
        "<polygon points='0 0, 9 3.5, 0 7' fill='#c00'/></marker></defs>",
        f'<rect width="{w}" height="{h}" fill="white"/>',
    ]
    if verdict is not None:
        out.append(
            f'<text x="{pad}" y="18" font-family="sans-serif" font-size="13" font-weight="bold" '
            f'fill="#c00">{esc(Verdict(verdict).value)}</text>'
        )
    for i, s in enumerate(path):
        x = pad + i * (bw + gap)
        y = pad + 26
        out.append(
            f'<rect x="{x}" y="{y}" width="{bw}" height="{bh}" rx="6" fill="#fdd" stroke="#c00" stroke-width="2"/>'
        )
        out.append(
            f'<text x="{x + bw / 2}" y="{y + 22}" text-anchor="middle" font-family="monospace" '
            f'font-size="11">{esc(_fmt(model.d(s)))}</text>'
        )
        out.append(
            f'<text x="{x + bw / 2}" y="{y + 40}" text-anchor="middle" font-family="sans-serif" '
            f'font-size="10" fill="#666">step {i}</text>'
        )
        if i:
            x0 = pad + (i - 1) * (bw + gap) + bw
            out.append(
                f'<line x1="{x0}" y1="{y + bh / 2}" x2="{x - 4}" y2="{y + bh / 2}" '
                f'stroke="#c00" stroke-width="2" marker-end="url(#a)"/>'
            )
            out.append(
                f'<text x="{(x0 + x) / 2}" y="{y + bh / 2 - 8}" text-anchor="middle" '
                f'font-family="sans-serif" font-size="10" fill="#c00">{esc(labels[i])}</text>'
            )
    out.append("</svg>")
    return "\n".join(out)
