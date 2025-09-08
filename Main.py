import os
import argparse
import unicodedata
from collections import deque, defaultdict
from typing import Set, Dict, List, Iterable, Tuple, Optional

# ================== CONSTANTES Y UTILIDADES ==================
EPSILON = 'ε'
UNICODE_MAP = {
    'ϵ': EPSILON, 'ɛ': EPSILON, 'ε': EPSILON,
    '∗': '*', '＋': '+', '？': '?', '｜': '|', '∣': '|',
    '（': '(', '）': ')', '·': '.', '•': '.'
}

def canon(s: str) -> str:
    if s is None:
        return ''
    s = unicodedata.normalize('NFKC', s)
    s = ''.join(UNICODE_MAP.get(ch, ch) for ch in s)
    s = ''.join(ch for ch in s if ch not in {' ', '\t', '\r', '\n'})
    return s

def read_expressions(path: str) -> List[Tuple[str, Optional[str]]]:
    if not os.path.exists(path):
        raise FileNotFoundError(f"No existe el archivo: {path}")
    exprs = []
    with open(path, 'r', encoding='utf-8') as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith('#'):
                continue
            if ',' in line:
                parts = line.split(',', 1)
                expr = parts[0].strip()
                w = parts[1].strip() if len(parts) > 1 else None
            else:
                expr = line
                w = None
            exprs.append((expr, w))
    return exprs

def ensure_dir(path: str):
    os.makedirs(path, exist_ok=True)

# ================== AST ==================
class ASTNode:
    def __init__(self, value):
        self.value = value

class OperandNode(ASTNode):
    def __init__(self, value):
        super().__init__(value)

class OperatorNode(ASTNode):
    def __init__(self, value, left=None, right=None):
        super().__init__(value)
        self.left = left
        self.right = right

class UnaryNode(ASTNode):
    def __init__(self, value, child=None):
        super().__init__(value)
        self.child = child

UNARY_OPS = {'*', '+', '?'}
BINARY_OPS = {'.', '|'}

def postfix_to_ast(postfix: str) -> ASTNode:
    stack = []
    for ch in postfix:
        if ch in UNARY_OPS:
            if not stack:
                raise ValueError("Postfix inválido: falta operando para operador unario")
            child = stack.pop()
            stack.append(UnaryNode(ch, child))
        elif ch in BINARY_OPS:
            if len(stack) < 2:
                raise ValueError("Postfix inválido: faltan operandos para operador binario")
            right = stack.pop()
            left = stack.pop()
            stack.append(OperatorNode(ch, left, right))
        else:
            stack.append(OperandNode(ch))

    if len(stack) != 1:
        raise ValueError("Postfix inválido: pila no terminó con un único elemento")
    return stack[0]

# ================== SHUNTING YARD ==================
OPERATORS = {'|', '.', '*', '+', '?', '(', ')'}
POSTFIX_UNARY = {'*', '+', '?'}

def _is_operand(ch: str) -> bool:
    return ch not in OPERATORS or ch == EPSILON

def add_explicit_concatenation(regex: str) -> str:
    result: List[str] = []
    prev = None
    for ch in regex:
        if ch == ' ' or ch == '\t' or ch == '\n':
            continue
        if prev is not None:
            if ((_is_operand(prev) or prev in {')', '*', '+', '?'}) and
                (_is_operand(ch) or ch == '(')):
                result.append('.')
        result.append(ch)
        prev = ch
    return ''.join(result)

def simple_infix_to_postfix(regex: str) -> str:
    prec = {'|': 1, '.': 2}
    out: List[str] = []
    stack: List[str] = []

    for ch in regex:
        if _is_operand(ch) and ch not in {'(', ')'}:
            out.append(ch)
        elif ch in POSTFIX_UNARY:
            out.append(ch)
        elif ch == '(':
            stack.append(ch)
        elif ch == ')':
            while stack and stack[-1] != '(':
                out.append(stack.pop())
            if not stack:
                raise ValueError("Paréntesis desbalanceados")
            stack.pop()
        elif ch in ('.', '|'):
            while stack and stack[-1] in prec and prec[stack[-1]] >= prec[ch]:
                out.append(stack.pop())
            stack.append(ch)
        else:
            raise ValueError(f"Símbolo inesperado en expresión: {ch}")

    while stack:
        top = stack.pop()
        if top in {'(', ')'}:
            raise ValueError("Paréntesis desbalanceados al final")
        out.append(top)

    return ''.join(out)

# ================== THOMPSON NFA ==================
class NFAState:
    def __init__(self):
        self.transitions: Dict[str, Set['NFAState']] = defaultdict(set)

    def add_transition(self, symbol: str, state: 'NFAState'):
        self.transitions[symbol].add(state)

class NFAFragment:
    def __init__(self, start: NFAState, accepts: Iterable[NFAState]):
        self.start = start
        self.accepts = set(accepts)

def collect_states(start: NFAState) -> Set[NFAState]:
    seen = set()
    stack = [start]
    while stack:
        s = stack.pop()
        if s in seen:
            continue
        seen.add(s)
        for dests in s.transitions.values():
            for d in dests:
                if d not in seen:
                    stack.append(d)
    return seen

def thompson_from_ast(node: ASTNode) -> NFAFragment:
    if isinstance(node, OperandNode):
        s = NFAState()
        f = NFAState()
        if node.value == EPSILON:
            s.add_transition(EPSILON, f)
        else:
            s.add_transition(node.value, f)
        return NFAFragment(s, [f])

    if isinstance(node, OperatorNode):
        if node.value == '.':
            left = thompson_from_ast(node.left)
            right = thompson_from_ast(node.right)
            for a in left.accepts:
                a.add_transition(EPSILON, right.start)
            return NFAFragment(left.start, right.accepts)

        if node.value == '|':
            left = thompson_from_ast(node.left)
            right = thompson_from_ast(node.right)
            s = NFAState()
            f = NFAState()
            s.add_transition(EPSILON, left.start)
            s.add_transition(EPSILON, right.start)
            for a in left.accepts:
                a.add_transition(EPSILON, f)
            for a in right.accepts:
                a.add_transition(EPSILON, f)
            return NFAFragment(s, [f])

    if isinstance(node, UnaryNode):
        child = thompson_from_ast(node.child)
        if node.value == '*':
            s = NFAState()
            f = NFAState()
            s.add_transition(EPSILON, child.start)
            s.add_transition(EPSILON, f)
            for a in child.accepts:
                a.add_transition(EPSILON, child.start)
                a.add_transition(EPSILON, f)
            return NFAFragment(s, [f])

        if node.value == '+':
            first = thompson_from_ast(node.child)
            star_node = UnaryNode('*', node.child)
            star_frag = thompson_from_ast(star_node)
            for a in first.accepts:
                a.add_transition(EPSILON, star_frag.start)
            return NFAFragment(first.start, star_frag.accepts)

        if node.value == '?':
            s = NFAState()
            f = NFAState()
            s.add_transition(EPSILON, child.start)
            s.add_transition(EPSILON, f)
            for a in child.accepts:
                a.add_transition(EPSILON, f)
            return NFAFragment(s, [f])

    raise ValueError(f"No se pudo construir NFA para nodo: {getattr(node,'value',node)}")

def epsilon_closure(states: Iterable[NFAState]) -> Set[NFAState]:
    stack = list(states)
    closure = set(stack)
    while stack:
        s = stack.pop()
        for nxt in s.transitions.get(EPSILON, []):
            if nxt not in closure:
                closure.add(nxt)
                stack.append(nxt)
    return closure

def move(states: Iterable[NFAState], symbol: str) -> Set[NFAState]:
    dest = set()
    for s in states:
        for nxt in s.transitions.get(symbol, []):
            dest.add(nxt)
    return dest

# ================== SUBSET CONSTRUCTION DFA ==================
class DFAState:
    def __init__(self, nfa_set):
        self.nfa_set = frozenset(nfa_set)
        self.transitions: Dict[str, 'DFAState'] = {}
        self.is_accept = False

class DFA:
    def __init__(self):
        self.start: DFAState = None
        self.states: List[DFAState] = []
        self.alphabet: Set[str] = set()

def nfa_to_dfa(nfa_frag: NFAFragment) -> DFA:
    alphabet = set()
    for s in collect_states(nfa_frag.start):
        for sym in s.transitions.keys():
            if sym != EPSILON:
                alphabet.add(sym)

    dfa = DFA()
    dfa.alphabet = alphabet

    start_set = epsilon_closure({nfa_frag.start})
    key_to_state: Dict[frozenset, DFAState] = {}

    def get_state(nfa_key: frozenset) -> DFAState:
        st = key_to_state.get(nfa_key)
        if st is not None:
            return st
        st = DFAState(nfa_key)
        st.is_accept = any(n in nfa_frag.accepts for n in nfa_key)
        key_to_state[nfa_key] = st
        dfa.states.append(st)
        return st

    dfa.start = get_state(frozenset(start_set))

    q = deque([dfa.start])
    visited = {dfa.start.nfa_set}

    while q:
        cur = q.popleft()
        for sym in alphabet:
            m = move(cur.nfa_set, sym)
            if not m:
                continue
            u = epsilon_closure(m)
            key = frozenset(u)
            dst = get_state(key)
            cur.transitions[sym] = dst
            if key not in visited:
                visited.add(key)
                q.append(dst)

    return dfa

# ================== DFA MINIMIZATION ==================
def minimize_dfa(dfa: DFA) -> DFA:
    if not dfa.states:
        return dfa

    alphabet = set(dfa.alphabet)
    accept = set([s for s in dfa.states if s.is_accept])
    nonaccept = set([s for s in dfa.states if not s.is_accept])

    P: List[Set[DFAState]] = []
    if accept:
        P.append(accept)
    if nonaccept:
        P.append(nonaccept)

    W: List[Set[DFAState]] = []
    if accept:
        W.append(set(accept))

    def trans_image(block: Set[DFAState], sym: str) -> Set[DFAState]:
        inv = set()
        for s in dfa.states:
            dst = s.transitions.get(sym)
            if dst in block:
                inv.add(s)
        return inv

    while W:
        A = W.pop()
        for sym in alphabet:
            X = trans_image(A, sym)
            newP = []
            for Y in P:
                inter = Y & X
                diff = Y - X
                if inter and diff:
                    newP.extend([inter, diff])
                    if Y in W:
                        W.remove(Y)
                        W.extend([inter, diff])
                    else:
                        W.append(inter if len(inter) <= len(diff) else diff)
                else:
                    newP.append(Y)
            P = newP

    rep_map: Dict[DFAState, DFAState] = {}
    for block in P:
        rep = next(iter(block))
        for s in block:
            rep_map[s] = rep

    min_dfa = DFA()
    min_dfa.alphabet = set(alphabet)

    min_states: Dict[DFAState, DFAState] = {}
    def get_min_state(rep: DFAState) -> DFAState:
        st = min_states.get(rep)
        if st is None:
            st = DFAState(rep.nfa_set)
            st.is_accept = rep.is_accept
            min_states[rep] = st
        return st

    min_start_rep = rep_map[dfa.start]
    min_dfa.start = get_min_state(min_start_rep)

    for block in P:
        rep = next(iter(block))
        msrc = get_min_state(rep)
        for sym, dst in rep.transitions.items():
            msrc.transitions[sym] = get_min_state(rep_map[dst])

    min_dfa.states = list(min_states.values())
    return min_dfa

# ================== SIMULATION ==================
def simulate_nfa(nfa: NFAFragment, w: str) -> bool:
    current = epsilon_closure({nfa.start})
    for ch in w:
        current = epsilon_closure(move(current, ch))
        if not current:
            return False
    return any(s in nfa.accepts for s in current)

def simulate_dfa(dfa: DFA, w: str) -> bool:
    cur = dfa.start
    if cur is None:
        return False
    for ch in w:
        if ch not in dfa.alphabet:
            return False
        if ch not in cur.transitions:
            return False
        cur = cur.transitions[ch]
    return cur.is_accept

# ================== VISUALIZATION ==================
def _render_graphviz(dot, filename: str, kind: str):
    try:
        dot.render(filename, format='png', cleanup=True)
        print(f"{kind} guardado como {filename}.png")
    except Exception as e:
        print(f"Error al renderizar {kind} (Graphviz). Se guardará DOT.")
        try:
            with open(f"{filename}.dot", "w", encoding="utf-8") as f:
                f.write(dot.source)
            print(f"DOT guardado como {filename}.dot")
        except Exception as e2:
            print("No se pudo guardar DOT:", e2)

def visualize_ast(root: ASTNode, filename: str = "ast"):
    try:
        import graphviz
    except Exception:
        print("Graphviz no disponible para AST.")
        return

    dot = graphviz.Digraph(comment='AST de la ER')
    counter = {'i': 0}

    def add(node: ASTNode):
        i = counter['i']; counter['i'] += 1
        name = f"n{i}"
        label = node.value
        dot.node(name, label)
        if isinstance(node, OperatorNode):
            left = add(node.left)
            right = add(node.right)
            dot.edge(name, left)
            dot.edge(name, right)
        elif isinstance(node, UnaryNode):
            child = add(node.child)
            dot.edge(name, child)
        return name

    add(root)
    _render_graphviz(dot, filename, "AST")

def draw_nfa(nfa: NFAFragment, filename: str = "nfa"):
    try:
        import graphviz
    except Exception:
        print("Graphviz no disponible para NFA.")
        return

    dot = graphviz.Digraph(comment='NFA (Thompson)')
    dot.attr(rankdir='LR')
    states = list(collect_states(nfa.start))
    id_map: Dict[object, str] = {s: f"S{i}" for i, s in enumerate(states)}

    for s in states:
        shape = 'doublecircle' if s in nfa.accepts else 'circle'
        style = 'filled' if s is nfa.start else ''
        fill = 'lightgrey' if s is nfa.start else ''
        if style:
            dot.node(id_map[s], id_map[s], shape=shape, style=style, fillcolor=fill)
        else:
            dot.node(id_map[s], id_map[s], shape=shape)

    for s in states:
        for sym, dests in s.transitions.items():
            for d in dests:
                dot.edge(id_map[s], id_map[d], label=sym)

    _render_graphviz(dot, filename, "NFA")

def draw_dfa(dfa: DFA, filename: str = "dfa"):
    try:
        import graphviz
    except Exception:
        print("Graphviz no disponible para DFA.")
        return

    dot = graphviz.Digraph(comment='DFA (Subconjuntos)')
    dot.attr(rankdir='LR')
    id_map: Dict[object, str] = {st: f"Q{i}" for i, st in enumerate(dfa.states)}

    for st in dfa.states:
        shape = 'doublecircle' if st.is_accept else 'circle'
        style = 'filled' if st is dfa.start else ''
        fill = 'lightgrey' if st is dfa.start else ''
        if style:
            dot.node(id_map[st], id_map[st], shape=shape, style=style, fillcolor=fill)
        else:
            dot.node(id_map[st], id_map[st], shape=shape)

    for st in dfa.states:
        for sym, dst in st.transitions.items():
            dot.edge(id_map[st], id_map[dst], label=sym)

    _render_graphviz(dot, filename, "DFA")

# ================== MAIN PROCESSING ==================
def process_expression(regex_raw: str, w: str, index: int, outdir: str):
    regex = canon(regex_raw)
    print(f"\n[{index}] r = {regex}")

    regex_c = add_explicit_concatenation(regex)
    print(f"    (concatenación explícita) -> {regex_c}")

    postfix = simple_infix_to_postfix(regex_c)
    print(f"    postfix -> {postfix}")

    expr_dir = os.path.join(outdir, f"expr_{index}")
    ensure_dir(expr_dir)

    ast = postfix_to_ast(postfix)
    visualize_ast(ast, os.path.join(expr_dir, "ast"))

    nfa_frag = thompson_from_ast(ast)
    draw_nfa(nfa_frag, os.path.join(expr_dir, "nfa"))

    dfa = nfa_to_dfa(nfa_frag)
    draw_dfa(dfa, os.path.join(expr_dir, "dfa"))

    min_dfa = minimize_dfa(dfa)
    draw_dfa(min_dfa, os.path.join(expr_dir, "dfa_min"))

    if w is None:
        try:
            w = input("    Ingrese w para simular (vacío para omitir): ").strip()
            w = canon(w)
        except Exception:
            w = ''

    if w:
        ok_nfa = simulate_nfa(nfa_frag, w)
        print(f"    [AFN ] '{w}' ∈ L(r)? -> {'sí' if ok_nfa else 'no'}")

        ok_dfa = simulate_dfa(dfa, w)
        print(f"    [AFD ] '{w}' ∈ L(r)? -> {'sí' if ok_dfa else 'no'}")

        ok_min = simulate_dfa(min_dfa, w)
        print(f"    [AFD↓] '{w}' ∈ L(r)? -> {'sí' if ok_min else 'no'}")
    else:
        print("    (Simulación omitida)")

def main():
    parser = argparse.ArgumentParser(
        description="Proyecto TC: ER -> AFN -> AFD -> AFD_min + simulación"
    )
    parser.add_argument(
        "--input", "-i", default="expresiones.txt",
        help="Archivo de expresiones (una por línea). Por defecto: expresiones.txt"
    )
    parser.add_argument(
        "--outdir", "-o", default="out",
        help="Carpeta de salida para imágenes (por defecto: out)"
    )
    parser.add_argument(
        "--string", "-s", 
        help="Cadena a evaluar en todas las expresiones (sobrescribe las del archivo)"
    )
    args = parser.parse_args()

    ensure_dir(args.outdir)

    try:
        exprs = read_expressions(args.input)
    except Exception as e:
        print("Error leyendo expresiones:", e)
        return

    print(f"Se encontraron {len(exprs)} expresiones en {args.input}.")

    if args.string is not None:
        w_global = canon(args.string)
    else:
        w_global = None

    for i, (raw, w_file) in enumerate(exprs, start=1):
        w_to_use = w_global if w_global is not None else w_file
        try:
            process_expression(raw, w_to_use, i, args.outdir)
        except Exception as e:
            print(f"[{i}] Error procesando expresión '{raw}': {e}")

if __name__ == "__main__":
    main()