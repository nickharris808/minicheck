"""minicheck core — explicit-state safety/liveness checking and optional SMT induction.

Model shape: a `Protocol` is a state vector (a tuple of named fields), an initial state, a transition
function returning labelled successors, a dict of safety invariants, and an optional liveness goal.
Everything is finite and explicit; reachability is a breadth-first sweep, so a counterexample is always
a SHORTEST one.

The BFS half depends only on the standard library. The induction half imports z3 lazily and is optional:
`z3_available()` reports whether it can run, and every z3 entry point degrades cleanly when it cannot.
"""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass
from typing import Callable, Optional


class SearchIncomplete(Exception):
    """The state-space sweep could not be completed, so no exhaustive verdict is available.

    Signals "I stopped looking", never "there is nothing there". `check_safety` catches this to
    downgrade an unrefuted invariant from ``holds=True`` to ``holds=None``; a counterexample already
    found stays valid, because a witness does not depend on the search finishing.

    Subclassed by `StateSpaceExceeded` here and by `spec.IntBoundExceeded`.
    """


class StateSpaceExceeded(SearchIncomplete, RuntimeError):
    """The reachable set grew past `max_states`. Also a RuntimeError, for callers that catch that."""


@dataclass
class Protocol:
    name: str
    candidate: bool
    fields: tuple  # names of state components (readable traces)
    initial: tuple
    transitions: Callable  # state(tuple) -> list[(label:str, next_state:tuple)]
    invariants: dict  # name -> predicate(dict)->bool   (safety)
    goal: Optional[Callable] = None  # predicate(dict)->bool           (liveness target)
    fair: bool = True  # liveness assumes weak fairness of enabled transitions
    assumption: Optional[Callable] = None  # predicate(dict)->bool: env contract (assume-guarantee; S5)

    def d(self, s):
        return dict(zip(self.fields, s))


def _reachable(model: Protocol, max_states=200000):
    """BFS the reachable state space; return (states set, parent map, order list)."""
    seen = {model.initial: (None, None)}  # state -> (prev_state, label)
    order = [model.initial]
    q = deque([model.initial])
    while q:
        s = q.popleft()
        for label, ns in model.transitions(s):
            if ns not in seen:
                seen[ns] = (s, label)
                order.append(ns)
                q.append(ns)
                if len(seen) > max_states:
                    raise StateSpaceExceeded(f"state space > {max_states}")
    return seen, order


def _trace(parent, target):
    """Reconstruct [(label, state_dict)] path from initial to target."""
    path = []
    s = target
    while s is not None:
        prev, label = parent[s]
        path.append((label, s))
        s = prev
    path.reverse()
    return path


def check_safety(model: Protocol, max_states: int = 200000) -> dict:
    """For each invariant, exhaustively look for a reachable violating state; return shortest CEX.

    Three-valued, and the asymmetry is deliberate. Refuting a safety property and proving one need
    different amounts of evidence:

    * ``holds=False`` — a violating state was reached. The counterexample trace is a witness, so this
      is sound even if the sweep never finished. A bug found in a partial search is still a bug.
    * ``holds=True`` — the sweep completed and no state violated the invariant. This one *requires*
      exhaustiveness, which is why it is only issued when the whole space was enumerated.
    * ``holds=None`` — the search hit `max_states`, or the model refused to expand (an unbounded
      integer field), before any violation appeared. Undetermined: absence of a counterexample in a
      truncated search is not evidence of absence. ``incomplete_reason`` says what stopped it.

    So a model too big to enumerate still yields real counterexamples, and never yields a false
    "proved safe".
    """
    invariants = list(model.invariants.items())
    parent = {model.initial: (None, None)}
    order = [model.initial]
    cex: dict = {}
    incomplete = None

    def _scan(state):
        """Record the first violation of each invariant; BFS order makes it a shortest one."""
        d = model.d(state)
        for name, pred in invariants:
            if name in cex:
                continue
            try:
                ok = pred(d)
            except Exception as e:
                raise ValueError(f"invariant {name!r} raised on state {d!r}: {e}") from e
            if not ok:
                cex[name] = [{"label": lb, "state": model.d(st)} for lb, st in _trace(parent, state)]

    try:
        _scan(model.initial)
        q = deque([model.initial])
        while q:
            s = q.popleft()
            for label, ns in model.transitions(s):
                if ns not in parent:
                    if len(parent) >= max_states:
                        raise StateSpaceExceeded(f"state space > {max_states}")
                    parent[ns] = (s, label)
                    order.append(ns)
                    _scan(ns)
                    q.append(ns)
    except SearchIncomplete as e:
        # The sweep stopped early. Anything already witnessed stands; anything unrefuted becomes
        # undetermined rather than proved.
        incomplete = f"{type(e).__name__}: {e}"

    out = {
        "reachable_states": len(parent),
        "exhaustive": incomplete is None,
        "properties": {},
    }
    if incomplete:
        out["incomplete_reason"] = incomplete
    for name, _ in invariants:
        if name in cex:
            # A witness is a witness whether or not the sweep finished.
            out["properties"][name] = {"holds": False, "counterexample": cex[name]}
        elif incomplete is None:
            out["properties"][name] = {"holds": True, "counterexample": None}
        else:
            out["properties"][name] = {
                "holds": None,
                "counterexample": None,
                "reason": f"search did not complete ({incomplete}); no violation was found in the "
                f"{len(parent)} states explored, but that is not a proof of absence",
            }
    return out


def check_liveness(model: Protocol) -> dict:
    """Sound AG-EF check: every reachable state must be able to reach a goal state (co-reachability).
    A reachable state that cannot reach the goal is a liveness 'trap' -> violation with a witness.

    Three-valued, for the same reason `check_safety` is. AG-EF is a claim about EVERY reachable
    state, so it cannot be established from a search that stopped early — a trap might sit in the
    part that was never explored. An incomplete sweep therefore returns ``holds=None``.

    A model with no goal also returns ``holds=None``. "You never told me what to reach" is an
    absent question, not a satisfied property.
    """
    if model.goal is None:
        return {
            "holds": None,
            "note": "no goal defined, so liveness is undetermined (not vacuously satisfied); "
            "set Protocol.goal to ask a liveness question",
        }
    try:
        parent, order = _reachable(model)
    except SearchIncomplete as e:
        # Unlike safety, there is no partial result worth keeping: a trap witness found in a
        # truncated sweep is still real, but establishing that NO trap exists needs the whole space,
        # and the traps we could name are exactly the ones we already explored.
        return {
            "holds": None,
            "note": "the reachable-state sweep did not finish, so AG-EF could not be decided",
            "incomplete_reason": f"{type(e).__name__}: {e}",
        }
    # build forward edges and reverse edges
    fwd = {s: [] for s in parent}
    for s in parent:
        for _, ns in model.transitions(s):
            if ns in fwd:
                fwd[s].append(ns)
    goals = [s for s in parent if model.goal(model.d(s))]
    # backward BFS from goals -> co-reachable set
    rev = {s: [] for s in parent}
    for s in fwd:
        for ns in fwd[s]:
            rev[ns].append(s)
    co = set(goals)
    q = deque(goals)
    while q:
        s = q.popleft()
        for p in rev[s]:
            if p not in co:
                co.add(p)
                q.append(p)
    trap = next((s for s in order if s not in co), None)
    if trap is None:
        return {"holds": True, "reachable_states": len(parent), "goal_states": len(goals)}
    tr = _trace(parent, trap)
    return {
        "holds": False,
        "reachable_states": len(parent),
        "counterexample": [{"label": lb, "state": model.d(st)} for lb, st in tr],
        "note": "reachable state from which the goal can never be reached (liveness trap)",
    }


def check_bounded_time(model: Protocol, bound: int, max_states: int = 200000) -> dict:
    """A goal state must be reachable from init within `bound` steps (BFS depth).

    Carries the same `max_states` guard as `_reachable`: an unbounded model would otherwise consume
    memory until the process dies, and a partial sweep that ran out of room must not report a verdict.

    A model with no goal returns ``holds=None`` — undetermined, not True. There is no evidence either
    way about a deadline for an event the model never names.
    """
    if model.goal is None:
        return {
            "holds": None,
            "steps_to_goal": None,
            "bound": bound,
            "note": "no goal defined, so bounded-time is undetermined (not vacuously satisfied)",
        }
    depth = {model.initial: 0}
    q = deque([model.initial])
    best = None
    while q:
        s = q.popleft()
        if model.goal(model.d(s)):
            best = depth[s]
            break
        for _, ns in model.transitions(s):
            if ns not in depth:
                depth[ns] = depth[s] + 1
                q.append(ns)
                if len(depth) > max_states:
                    raise StateSpaceExceeded(
                        f"state space > {max_states} while searching for the goal; the sweep was not "
                        f"exhaustive, so no bounded-time verdict is available. Raise max_states or "
                        f"shrink the model."
                    )
    return {"holds": best is not None and best <= bound, "steps_to_goal": best, "bound": bound}


# --------------- z3 SMT inductive-invariant proof ---------------
def z3_available() -> bool:
    try:
        import z3  # noqa: F401

        return True
    except Exception:
        return False


def _var_names(v) -> set:
    """Names of the z3 declarations in a var container (dict, list or tuple)."""
    vals = v.values() if isinstance(v, dict) else (v if isinstance(v, (list, tuple)) else [v])
    return {str(x) for x in vals}


def _vacuity_check(v, vn, init, trans, inv, timeout_ms):
    """Return (ok, reason). Detects the encodings under which every proof obligation is vacuous.

    An UNSAT antecedent makes ``Inv & T => Inv'`` valid for reasons that have nothing to do with the
    invariant. The classic way to hit this by accident is to return the *same* variables for the
    current and next state, so ``x' == x + 1`` is unsatisfiable and every step obligation discharges.
    A proof that holds because its premise is impossible is not a proof of anything.
    """
    import z3

    shared = _var_names(v) & _var_names(vn)
    if shared:
        return False, (
            f"current- and next-state variables overlap on {sorted(shared)}; decls() must return two "
            f"DISJOINT copies of the state, otherwise the transition relation is unsatisfiable and "
            f"every obligation is vacuously valid"
        )

    def _sat(expr, what):
        s = z3.Solver()
        if timeout_ms is not None:
            s.set("timeout", timeout_ms)
        s.add(expr)
        r = s.check()
        if r == z3.unsat:
            return False, f"{what} is unsatisfiable, so every proof obligation built on it is vacuous"
        if r == z3.unknown:
            return False, f"z3 returned unknown while checking that {what} is satisfiable"
        return True, ""

    obligations = (
        (trans(v, vn), "the transition relation"),
        (inv(v), "the invariant"),
        (init(v), "the initial-state predicate"),
    )
    for expr, what in obligations:
        ok, why = _sat(expr, what)
        if not ok:
            return False, why
    return True, ""


def prove_inductive(decls, init, trans, inv, timeout_ms: int | None = None):
    """Prove an inductive invariant with z3.

    decls() -> (vars, vars_next); init(vars) -> z3 Bool; trans(vars,vars_next) -> z3 Bool;
    inv(vars) -> z3 Bool.

    Returns ``{'available', 'base_case', 'inductive_step', 'proven', 'vacuous', 'reason'}``.
    ``proven`` is True only when both obligations discharge AND the encoding is non-vacuous.

    Two ways this refuses instead of answering:

    * **Vacuity.** Before proving anything, the encoding is checked for the failure modes that make
      the obligations trivially valid — overlapping current/next variables, an unsatisfiable
      transition relation, an unsatisfiable invariant or initial predicate. Any of these returns
      ``proven=False, vacuous=True`` with the reason named. Previously such an encoding returned
      ``proven=True``, which is a proof of nothing reported as a proof.
    * **Unknown.** A z3 ``unknown`` (including a timeout) is not ``unsat``, so it never counts as a
      discharged obligation. ``proven`` is False and ``reason`` says which obligation was undecided.

    timeout_ms: fail-closed live-request cap. Default None = unbounded (offline proof gates keep
    their full budgets). Only the API seam passes a value; all offline callers omit it.
    """
    if not z3_available():
        return {
            "available": False,
            "proven": None,
            "reason": "z3 is not installed; no inductive proof was attempted (pip install z3-solver)",
        }
    import z3

    v, vn = decls()

    non_vacuous, why = _vacuity_check(v, vn, init, trans, inv, timeout_ms)
    if not non_vacuous:
        return {
            "available": True,
            "base_case": None,
            "inductive_step": None,
            "proven": False,
            "vacuous": True,
            "reason": why,
        }

    def _discharge(assertions):
        """An obligation discharges only on UNSAT. `unknown` is undecided, never success."""
        s = z3.Solver()
        if timeout_ms is not None:
            s.set("timeout", timeout_ms)
        for a in assertions:
            s.add(a)
        r = s.check()
        return r == z3.unsat, r

    base_ok, base_r = _discharge([init(v), z3.Not(inv(v))])  # Init => Inv
    step_ok, step_r = _discharge([inv(v), trans(v, vn), z3.Not(inv(vn))])  # Inv & T => Inv'

    undecided = [n for n, r in (("base_case", base_r), ("inductive_step", step_r)) if r == z3.unknown]
    reason = ""
    if undecided:
        reason = f"z3 returned unknown for {', '.join(undecided)}; undecided is not proven"
    elif not (base_ok and step_ok):
        failed = [n for n, ok in (("base_case", base_ok), ("inductive_step", step_ok)) if not ok]
        reason = f"{', '.join(failed)} did not discharge (a counterexample to induction exists)"

    return {
        "available": True,
        "base_case": base_ok,
        "inductive_step": step_ok,
        "proven": bool(base_ok and step_ok),
        "vacuous": False,
        "reason": reason,
    }


def prove_k_induction(mk, init, trans, inv, k=2, timeout_ms: int | None = None):
    """Prove a safety invariant by k-induction (stronger than 1-induction).

    mk(suffix)->vardict builds a fresh copy of the state vars; init(v), trans(v,vn), inv(v) are
    z3 predicates. Base case: no violation in the first k states reachable from Init. Step: if Inv
    holds in k consecutive states linked by T, it holds in the (k+1)-th. Returns base/step/proven.
    Used as a fallback when a 1-step inductive invariant is too weak; reported alongside the
    1-induction verdict so the report is explicit about which strength was needed.

    SOUND, NOT COMPLETE -- and the distinction is load-bearing, so it is stated here rather than
    left implicit (audit note, 2026-07-26).

    This procedure adds NO simple-path (pairwise-distinct) constraint to the step unroll. That makes
    it *sound*: ``proven=True`` means the invariant genuinely holds. It does NOT make it *complete*:
    ``proven=False`` means only "not provable at this k", never "the property fails", and there is no
    k at which the step is guaranteed to close.

    **Use it in the positive direction only.** Requiring a *sound* procedure to succeed is valid, and
    the incompleteness makes such a check CONSERVATIVE -- it may decline to credit something true, but
    it is never wrong. Do not draw a conclusion from ``proven=False``.

    If you need "failure to find implies absence", you need a *complete* variant: add a simple-path
    (pairwise-distinct) constraint to the unroll, which bounds termination by the longest simple path
    and therefore is complete on a finite system. This procedure deliberately does not do that,
    because the constraint is expensive and most callers only need soundness.

    timeout_ms: fail-closed live cap (default None = unbounded; see prove_inductive).
    """
    if not z3_available():
        return {"available": False, "proven": None}
    import z3

    st = [mk(f"_{i}") for i in range(k + 1)]
    sb = z3.Solver()
    if timeout_ms is not None:
        sb.set("timeout", timeout_ms)
    sb.add(init(st[0]))
    for i in range(k - 1):
        sb.add(trans(st[i], st[i + 1]))
    sb.add(z3.Or(*[z3.Not(inv(st[i])) for i in range(k)]))
    base_ok = sb.check() == z3.unsat
    ss = z3.Solver()
    if timeout_ms is not None:
        ss.set("timeout", timeout_ms)
    for i in range(k):
        ss.add(inv(st[i]))
        ss.add(trans(st[i], st[i + 1]))
    ss.add(z3.Not(inv(st[k])))
    step_ok = ss.check() == z3.unsat
    return {
        "available": True,
        "k": k,
        "base_case": base_ok,
        "inductive_step": step_ok,
        "proven": bool(base_ok and step_ok),
    }


# --------------- timed model checking (z3 over the reals) ---------------
def check_timed_safety(builder, timeout_ms: int | None = None) -> dict:
    """Prove a bounded-latency / deadline property with z3 real-arithmetic ("timed automaton" style).

    builder() -> (clock_vars, constraints, deadline_expr, delay_expr): `constraints` bound each phase
    duration to a real interval [lo, hi]; `delay_expr` is the worst-case latency of the critical
    operation along the modeled path; `deadline_expr` is the budget. We ask z3 whether
    (constraints ∧ delay > deadline) is satisfiable:
      * UNSAT  -> the deadline is met on every admissible schedule -> PROVEN bounded-latency.
      * SAT    -> a concrete TIMED COUNTEREXAMPLE (clock valuations) that blows the deadline.
    This is a genuine proof over a dense (real-valued) time domain, not a finite sampling.
    """
    if not z3_available():
        return {"available": False, "engine": "z3-real", "proven": None, "note": "z3 not installed"}
    import z3

    clocks, cons, deadline, delay = builder()
    s = z3.Solver()
    if timeout_ms is not None:
        s.set("timeout", timeout_ms)
    for c in cons:
        s.add(c)
    s.add(delay > deadline)
    r = s.check()
    if r == z3.unsat:
        return {"available": True, "engine": "z3-real", "deadline_met": True, "proven": True, "counterexample": None}
    if r == z3.sat:
        mdl = s.model()
        cex = {}
        for v in clocks:
            try:
                cex[str(v)] = str(mdl.eval(v, model_completion=True))
            except Exception:
                cex[str(v)] = "?"
        return {"available": True, "engine": "z3-real", "deadline_met": False, "proven": False, "counterexample": cex}
    return {"available": True, "engine": "z3-real", "deadline_met": None, "proven": None, "note": "z3 returned unknown"}


def prove_latency_bound(burst, arr_rate, svc_rate, svc_latency, deadline) -> dict:
    """Deterministic network-calculus delay bound (closed form, no solver needed).

    Arrival curve  alpha(t) = burst + arr_rate * t   (leaky-bucket / token-bucket regulated flow).
    Service curve  beta(t)  = svc_rate * (t - svc_latency)+   (rate-latency server).
    For a stable system (arr_rate < svc_rate) the worst-case delay is the horizontal deviation
    h(alpha, beta) = svc_latency + burst / svc_rate. Returns the bound and whether it meets the
    deadline. This is the analytic guarantee that complements the z3 timed proof.
    """
    if svc_rate <= arr_rate:
        return {
            "method": "network-calculus",
            "stable": False,
            "delay_bound": float("inf"),
            "deadline": deadline,
            "holds": False,
            "note": "unstable: arrival rate >= service rate (backlog grows unboundedly)",
        }
    delay_bound = svc_latency + (burst / svc_rate)
    return {
        "method": "network-calculus (rate-latency server, leaky-bucket arrival)",
        "stable": True,
        "delay_bound": delay_bound,
        "deadline": deadline,
        "holds": delay_bound <= deadline,
    }


# --------------- probabilistic / statistical model checking ---------------
def check_probabilistic(trans_probs, start, miss_states, eps, success_states=None) -> dict:
    """Exact P(eventually reach a miss state) on an absorbing DTMC, vs a target eps.

    trans_probs: dict state -> list[(prob, next_state)] (rows sum to 1). `miss_states` are absorbing
    "deadline-miss" states (h=1); every other absorbing state (or `success_states`) has h=0. Solving
    the linear system h(s) = sum_s' P(s,s') h(s') with the boundary conditions gives the exact hitting
    probability — an absorbing-Markov-chain result, not a simulation. Engine label is honest.
    """
    states = list(trans_probs.keys())
    miss = set(miss_states)
    for s in states:
        for _, ns in trans_probs[s]:
            if ns not in trans_probs and ns not in miss:
                # absorbing sink not explicitly listed -> treat as success (h=0)
                pass
    idx = {s: i for i, s in enumerate(states)}
    n = len(states)
    # Build (I - Q) h = b  where for non-miss states h(s) - sum P h(s') = 0, miss states h=1.
    A = [[0.0] * n for _ in range(n)]
    b = [0.0] * n
    for s in states:
        i = idx[s]
        if s in miss:
            A[i][i] = 1.0
            b[i] = 1.0
            continue
        A[i][i] += 1.0
        for p, ns in trans_probs[s]:
            if ns in miss:
                b[i] += p  # contributes p*1
            elif ns in idx:
                A[i][idx[ns]] -= p  # -p * h(ns)
            # ns absorbing-success or unlisted sink -> p*0, nothing to add
    if start not in idx:
        raise ValueError(f"start state {start!r} is not one of the {n} states in trans_probs")
    try:
        h = _solve_linear(A, b)
    except SingularSystem as e:
        # No unique solution => no hitting probability. Abstain loudly rather than report a number.
        return {
            "engine": "absorbing-markov-chain (exact linear solve)",
            "p_miss": None,
            "eps": float(eps),
            "holds": None,
            "n_states": n,
            "reason": f"the chain's linear system has no unique solution ({e}); no exact hitting "
            f"probability exists, so no verdict is issued",
        }
    p_miss = float(h[idx[start]])
    if not (0.0 - 1e-9 <= p_miss <= 1.0 + 1e-9):
        # A probability outside [0,1] means the input was not a stochastic matrix. Do not report it.
        return {
            "engine": "absorbing-markov-chain (exact linear solve)",
            "p_miss": None,
            "eps": float(eps),
            "holds": None,
            "n_states": n,
            "reason": f"solved hitting probability {p_miss!r} is outside [0, 1]; trans_probs is not a "
            f"valid stochastic matrix (do the rows sum to 1?), so the result is not a probability",
        }
    p_miss = min(1.0, max(0.0, p_miss))
    return {
        "engine": "absorbing-markov-chain (exact linear solve)",
        "p_miss": p_miss,
        "eps": float(eps),
        "holds": bool(p_miss < eps),
        "n_states": n,
    }


def check_statistical(trans_probs, start, miss_states, n_samples=20000, seed=12345, conf=0.99, horizon=200) -> dict:
    """Statistical model checking fallback: seeded Monte-Carlo estimate of P(reach miss) with a
    Hoeffding confidence half-width. Deterministic for a fixed seed. Honestly labeled as a
    statistical estimate (confidence `conf`), NOT an exhaustive proof — used when a chain is too
    large for the exact solve."""
    import math
    import random

    rng = random.Random(seed)
    miss = set(miss_states)
    hits = 0
    for _ in range(n_samples):
        s = start
        for _step in range(horizon):
            if s in miss:
                hits += 1
                break
            row = trans_probs.get(s)
            if not row:
                break  # absorbing non-miss
            r = rng.random()
            acc = 0.0
            nxt = row[-1][1]
            for p, ns in row:
                acc += p
                if r <= acc:
                    nxt = ns
                    break
            s = nxt
    p = hits / n_samples
    half = math.sqrt(math.log(2.0 / (1.0 - conf)) / (2.0 * n_samples))  # Hoeffding bound
    return {
        "engine": f"statistical-monte-carlo (n={n_samples}, conf={conf})",
        "p_miss_est": p,
        "confidence": conf,
        "half_width": half,
        "p_miss_upper": min(1.0, p + half),
        # No `holds` key by design. This is an estimate with a confidence interval, not a proof, and
        # emitting a boolean next to it would invite exactly the confusion the interval exists to
        # prevent. Compare `p_miss_upper` against your target yourself, and note that the guarantee
        # is (1 - conf) two-sided over the sampling, not over the model.
        "is_proof": False,
        "note": "statistical estimate, NOT an exhaustive proof; use check_probabilistic for an exact verdict",
    }


# --------------- v13: PARAMETRIC (closed-form-in-N) probabilistic reasoning ---------------
def parametric_hitting_closed_form(q, N):
    """CLOSED-FORM hitting probability, parametric in the horizon/multiplicity N — valid for ALL N, not a
    fixed-horizon Monte-Carlo slice. For an i.i.d. per-attempt residual-failure probability q in [0,1]
    (e.g. per-HARQ-round residual BLER), the probability that N independent attempts ALL fail (a deadline
    miss after N retries) is exactly q^N, and the success-within-N probability is 1 - q^N. Monotone
    decreasing in N. The exact attempt budget to reach a target failure eps is N*(eps)=ceil(ln eps/ln q).
    This is an absorbing-Markov-chain result in closed form, NOT a simulation."""
    q = float(q)
    N = int(N)
    p_miss = q**N
    return {
        "q": q,
        "N": N,
        "p_miss_closed_form": float(p_miss),
        "p_success_within_N": float(1.0 - p_miss),
        "formula": "P(miss after N i.i.d. attempts) = q^N (closed form in N)",
        "monotone_decreasing_in_N": bool(q <= 1.0),
        "engine": "closed-form parametric DTMC (geometric retry chain)",
    }


def n_to_reach_target(q, eps):
    """Smallest N with q^N <= eps (the exact attempt budget for target failure eps). Closed form."""
    import math

    q = float(q)
    eps = float(eps)
    if not (0.0 < q < 1.0) or not (0.0 < eps < 1.0):
        return None
    return int(math.ceil(math.log(eps) / math.log(q)))


def retry_chain_exact(q, N):
    """Exact absorbing-DTMC P(reach miss) for the N-round retry chain, to CROSS-CHECK the q^N closed form
    (states 0..N-1 each fail->next w.p. q / success-absorb w.p. 1-q; state N-1 fail -> miss)."""
    trans = {}
    for i in range(N):
        nxt = (i + 1) if i + 1 < N else "MISS"
        trans[i] = [(float(q), nxt), (float(1.0 - q), "SUCCESS")]
    return check_probabilistic(trans, 0, ["MISS"], eps=1.0)["p_miss"]


def empirical_bernstein_anytime(var_hat, n, delta=0.05, rng=1.0):
    """TIME-UNIFORM (anytime-valid) empirical-Bernstein confidence half-width — valid SIMULTANEOUSLY for
    every sample size (so you may stop adaptively), unlike the FIXED-n Hoeffding bound. Form (Howard,
    Ramdas, McAuliffe, Sekhon 2021; Maurer-Pontil empirical Bernstein with an ln-ln peeling term):

        w(n) = sqrt(2 * Vhat * ell / n) + 3 * R * ell / n ,   ell = ln( ln(e n) / delta ),  R = range.

    It is variance-ADAPTIVE: when the observed variance Vhat is small (the reliability regime, rare
    misses) it is far tighter than Hoeffding's sqrt(ln(2/delta)/(2n)), AND it is anytime-valid. Returns
    both half-widths and which is tighter at this (Vhat, n, delta)."""
    import math

    n = int(n)
    if n < 1:
        return {
            "eb_anytime_halfwidth": float("inf"),
            "hoeffding_fixedn_halfwidth": float("inf"),
            "eb_tighter": False,
            "anytime_valid": True,
        }
    ell = math.log(math.log(math.e * n) / float(delta))
    ell = max(ell, 1e-12)
    eb = math.sqrt(2.0 * float(var_hat) * ell / n) + 3.0 * float(rng) * ell / n
    hoeff = math.sqrt(math.log(2.0 / float(delta)) / (2.0 * n))
    return {
        "eb_anytime_halfwidth": float(eb),
        "hoeffding_fixedn_halfwidth": float(hoeff),
        "eb_tighter": bool(eb < hoeff),
        "anytime_valid": True,
        "engine": "time-uniform empirical-Bernstein (Howard et al. 2021); anytime-valid",
    }


class SingularSystem(ArithmeticError):
    """The linear system has no unique solution, so no hitting probability can be reported.

    Raised instead of returning a number. The previous implementation swallowed numpy's
    ``LinAlgError`` and divided by a ``1e-15`` sentinel, so a singular system produced a finite,
    plausible-looking answer on the order of 1e15 with no error and no flag.
    """


def _solve_linear(A, b, tol: float = 1e-12):
    """Solve A x = b exactly-or-refuse. Never returns a value for a system that has none.

    Uses numpy when available and falls back to Gaussian elimination with partial pivoting. A
    singular or numerically-degenerate matrix raises `SingularSystem` rather than dividing by a
    sentinel: a chain whose linear system does not have a unique solution has no well-defined
    hitting probability, and inventing one is worse than saying so.
    """
    n = len(b)
    if n == 0:
        raise SingularSystem("empty linear system: nothing to solve")
    if any(len(row) != n for row in A) or len(A) != n:
        raise SingularSystem(f"linear system is not square: A is {len(A)}x{len(A[0]) if A else 0}, b has {n} entries")

    try:
        import numpy as np
    except ImportError:
        np = None

    if np is not None:
        try:
            arr = np.array(A, dtype=float)
            sol = np.linalg.solve(arr, np.array(b, dtype=float))
        except np.linalg.LinAlgError as e:
            raise SingularSystem(f"matrix is singular: {e}") from e
        if not np.all(np.isfinite(sol)):
            raise SingularSystem("solution contains non-finite entries; the system is degenerate")
        # A solved-but-ill-conditioned system is reported too: the digits are not there.
        cond = float(np.linalg.cond(arr))
        if not (cond < 1.0 / tol):
            raise SingularSystem(
                f"matrix is numerically singular (condition number {cond:.3g}); the solution would "
                f"carry no significant digits"
            )
        return [float(x) for x in sol]

    M = [list(row) + [b[i]] for i, row in enumerate(A)]
    for col in range(n):
        piv = max(range(col, n), key=lambda r: abs(M[r][col]))
        if abs(M[piv][col]) <= tol:
            raise SingularSystem(f"matrix is singular: no usable pivot in column {col}")
        M[col], M[piv] = M[piv], M[col]
        pv = M[col][col]
        for r in range(n):
            if r != col and M[r][col]:
                f = M[r][col] / pv
                M[r] = [M[r][k] - f * M[col][k] for k in range(n + 1)]
    out = []
    for i in range(n):
        if abs(M[i][i]) <= tol:
            raise SingularSystem(f"matrix is singular: zero pivot at row {i} after elimination")
        out.append(M[i][n] / M[i][i])
    return out


# --------------- refinement & composition ---------------
def check_refinement(impl: Protocol, spec: Protocol, abstraction) -> dict:
    """Prove `impl` refines `spec`: the abstraction maps every reachable impl state to a spec state,
    the initial impl state maps to the spec initial state, and every impl transition maps to a spec
    transition or a stutter (same abstract state). Establishes that the concrete procedure preserves
    the abstract safety contract. abstraction: impl-state-dict -> spec-state-tuple."""
    parent, order = _reachable(impl)
    spec_states = set(_reachable(spec)[0].keys())
    init_ok = abstraction(impl.d(impl.initial)) == spec.initial
    spec_trans = {s: {ns for _, ns in spec.transitions(s)} for s in spec_states}
    violations = []
    for s in order:
        a = abstraction(impl.d(s))
        if a not in spec_states:
            violations.append({"impl_state": impl.d(s), "reason": "abstract image not a spec state"})
            continue
        for lb, ns in impl.transitions(s):
            an = abstraction(impl.d(ns))
            if an != a and an not in spec_trans.get(a, set()):
                violations.append(
                    {
                        "label": lb,
                        "from": impl.d(s),
                        "to": impl.d(ns),
                        "reason": "impl step is neither a stutter nor a spec step",
                    }
                )
    return {
        "refines": init_ok and not violations,
        "initial_maps": init_ok,
        "impl_states": len(parent),
        "spec_states": len(spec_states),
        "violations": violations[:5],
    }


def check_composition(models, joint_invariants) -> dict:
    """Prove safety is preserved when several procedures run concurrently (interleaving product).

    models: list[Protocol] whose `fields` MUST be disjoint — this is checked, not assumed. The
    product interleaves each component's transitions over the combined state. `joint_invariants`
    (name->predicate(combined-dict)->bool) are checked over the whole reachable product — catching any
    EMERGENT cross-procedure counterexample that none of the components exhibits alone.

    Raises `ValueError` if two components share a field name. The combined state dict is keyed by
    field name, so a shared name silently collapses two independent variables into one: the product
    explored is not the product the caller described, and any verdict is about a different system.
    """
    if not models:
        raise ValueError("check_composition needs at least one model; an empty product has no meaning")

    seen_fields: dict = {}
    collisions: dict = {}
    for m in models:
        for f in m.fields:
            if f in seen_fields:
                collisions.setdefault(f, [seen_fields[f]]).append(m.name)
            else:
                seen_fields[f] = m.name
    if collisions:
        detail = "; ".join(f"{f!r} in {sorted(set(owners))}" for f, owners in sorted(collisions.items()))
        raise ValueError(
            f"composed models must have disjoint field names, but {detail}. The product state is keyed "
            f"by name, so shared names merge into one variable and the result would describe a different "
            f"system than the one you passed. Rename the fields (e.g. prefix each with its model name)."
        )

    fields = tuple(f for m in models for f in m.fields)
    sizes = [len(m.fields) for m in models]
    offs = [sum(sizes[:i]) for i in range(len(models))]
    initial = tuple(x for m in models for x in m.initial)

    def split(s):
        return [s[offs[i] : offs[i] + sizes[i]] for i in range(len(models))]

    def trans(s):
        parts = split(s)
        out = []
        for i, m in enumerate(models):
            for lb, ns in m.transitions(parts[i]):
                combo = list(parts)
                combo[i] = ns
                out.append((f"{m.name}:{lb}", tuple(x for p in combo for x in p)))
        return out

    prod = Protocol(
        name="+".join(m.name for m in models),
        candidate=True,
        fields=fields,
        initial=initial,
        transitions=trans,
        invariants=joint_invariants,
    )
    res = check_safety(prod)
    viol = {p: r["counterexample"] for p, r in res["properties"].items() if not r["holds"]}
    return {
        "composed": [m.name for m in models],
        "reachable_states": res["reachable_states"],
        "all_hold": not viol,
        "violated": list(viol),
        "counterexample": next(iter(viol.values()), None),
    }


def prove_composition_inductive(components, timeout_ms: int | None = None):
    """UNBOUNDED inductive proof that the joint safety invariant (the conjunction of each component's
    own safety invariant) holds over the ENTIRE reachable interleaving product — no state cap, no BFS.
    This is the unbounded analogue of `check_composition`: where that explores a finite BFS slice
    (bounded by max_states), this z3-proves Init => I and I & T_product => I' over the product of the
    SYMBOLIC component encodings, certifying joint safety at every reachable product state at any depth.

    `components`: list of z3 encoder dicts {mk, init, trans, inv}. Each
    component is given its OWN variable namespace (suffix _c{i}); the product interleaves — exactly one
    component steps while the others STUTTER (next == current). Because each component's transition
    constrains only its own next-state variables and the stutter pins the rest, the environment (the
    other components) cannot interfere with any component's invariant — the assume-guarantee
    decomposition is sound BY CONSTRUCTION (disjoint namespaces, verified below).

    Returns base/step/proven + the assume-guarantee soundness flag.

    ``proven`` is GATED on that flag. The non-interference argument above is what makes the
    decomposition sound, and it only holds when the namespaces really are disjoint — so if the check
    fails, the obligations may well discharge but they do not mean what the docstring says they mean.
    Previously the flag was computed and reported but never consulted, so a caller who trusted
    ``proven`` got a verdict whose stated justification did not apply.
    """
    if not z3_available():
        return {
            "available": False,
            "proven": None,
            "reason": "z3 is not installed; no compositional proof was attempted (pip install z3-solver)",
        }
    import z3

    n = len(components)
    if n == 0:
        return {
            "available": True,
            "n_components": 0,
            "proven": False,
            "assume_guarantee_sound": False,
            "reason": "no components supplied; an empty product proves nothing",
        }
    cur = [components[i]["mk"](f"_c{i}") for i in range(n)]
    nxt = [components[i]["mk"](f"_c{i}_n") for i in range(n)]

    # assume-guarantee soundness: the component variable namespaces are pairwise DISJOINT, so no
    # component's step can touch another's state (non-interference) -> the rely-guarantee decomposition
    # is sound and the joint invariant decomposes over the product.
    names = [{str(var) for var in c.values()} for c in cur]
    nxt_names = [{str(var) for var in c.values()} for c in nxt]
    overlaps = sorted(
        {v for i in range(n) for j in range(i + 1, n) for v in (names[i] & names[j])}
        # a component whose next-state vars collide with its own current-state vars makes the
        # stutter constraint self-contradictory, which is the compositional form of the C2 vacuity bug
        | {v for i in range(n) for v in (names[i] & nxt_names[i])}
    )
    disjoint = not overlaps

    joint_init = z3.And(*[components[i]["init"](cur[i]) for i in range(n)])
    joint_inv_cur = z3.And(*[components[i]["inv"](cur[i]) for i in range(n)])
    joint_inv_nxt = z3.And(*[components[i]["inv"](nxt[i]) for i in range(n)])

    def _same(a, b):
        return z3.And(*[b[k] == a[k] for k in a])

    moves = []
    for i in range(n):
        stutter = [_same(cur[j], nxt[j]) for j in range(n) if j != i]
        moves.append(z3.And(components[i]["trans"](cur[i], nxt[i]), *stutter))
    product_trans = z3.Or(*moves)

    sb = z3.Solver()
    if timeout_ms is not None:
        sb.set("timeout", timeout_ms)
    sb.add(joint_init)
    sb.add(z3.Not(joint_inv_cur))
    base_ok = sb.check() == z3.unsat  # Init => I
    ss = z3.Solver()
    if timeout_ms is not None:
        ss.set("timeout", timeout_ms)
    ss.add(joint_inv_cur)
    ss.add(product_trans)
    ss.add(z3.Not(joint_inv_nxt))
    step_ok = ss.check() == z3.unsat  # I & T_product => I'

    reason = ""
    if not disjoint:
        reason = (
            f"assume-guarantee soundness FAILED: variable namespaces overlap on {overlaps}. The "
            f"non-interference argument that justifies this decomposition does not apply, so the "
            f"obligations below carry no compositional meaning and `proven` is withheld."
        )
    elif not (base_ok and step_ok):
        failed = [n_ for n_, ok in (("base_case", base_ok), ("inductive_step", step_ok)) if not ok]
        reason = f"{', '.join(failed)} did not discharge"

    return {
        "available": True,
        "n_components": n,
        "base_case": base_ok,
        "inductive_step": step_ok,
        # gated on soundness: the obligations only mean what we claim when the namespaces are disjoint
        "proven": bool(base_ok and step_ok and disjoint),
        "assume_guarantee_sound": bool(disjoint),
        "namespace_overlaps": overlaps,
        "reason": reason,
        "method": (
            "z3 inductive invariant over the UNBOUNDED interleaving product (no state cap); "
            "assume-guarantee non-interference by disjoint variable namespaces"
        ),
    }
