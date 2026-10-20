#!/usr/bin/env python3
"""reflow79.py [--apply] [--ascii] [--width 79] FILE...

Break lines longer than WIDTH so that the files respect the column limit,
keeping the token sequence identical (verified before writing).

  * Breaks happen at token boundaries (normally an existing space; also
    directly after `;` or `,` and next to a HOL quotation backquote), never
    inside a string, a char literal or a comment token.
  * Preference, evaluated at the shallowest bracket depth available on the
    line: after THEN/THENL/ORELSE in code; after `;` (continuation aligned
    under the first element of the enclosing bracket); code-level breaks
    next to a quotation; before a trailing (* comment *); inside a term after
    the loosest binary operator available (<=> before ==> before \\/ before
    /\\ before , before =), before `then`/`else`, after `in`; any other
    boundary at the shallowest depth; finally any boundary (aligned under the
    innermost open bracket).  Tiny heads and tails are avoided.
  * Single-line (* ... *) comments are re-wrapped as comments (banner
    comments padded to the width keep the padding); lines inside multi-line
    comments are wrapped at word boundaries with the same indentation.
  * HOL quotations are tracked so that `(*)` inside a term is not taken for
    a comment.  --ascii replaces the few non-ASCII characters by ASCII text.

Without --apply it only reports.  Lines that cannot be fixed (one token or
string longer than the limit) are reported and left alone.  Invariant
checked per file: token sequence (comments removed, whitespace ignored,
strings intact) and comment word sequence unchanged; otherwise the file is
not written."""
import re
import sys

WIDTH = 79
OP_RANK = {'<=>': 0, '==>': 1, '\\/': 2, '/\\': 3, ',': 4, '=': 5,
           '<=': 5, '<': 5, '>': 5, '>=': 5, '+': 6, '-': 6}
TOKEN = re.compile(r"[A-Za-z0-9_']+|.")


# ---------------------------------------------------------------------------
def scan(line, st):
    """per-char (mode, depth) for a line, given the state at its start;
    mode c=code s=string q=quotation k=comment.
    st = dict(mode, cdepth, after_comment, after_string);
    returns (states, st_after)"""
    mode, cdepth, depth = st['mode'], st['cdepth'], 0
    out = []
    i = 0
    n = len(line)
    while i < n:
        c = line[i]
        two = line[i:i+2]
        if mode == 'k':
            if two == '(*':
                cdepth += 1
                out += [('k', depth)] * 2
                i += 2
                continue
            if two == '*)':
                cdepth -= 1
                out += [('k', depth)] * 2
                i += 2
                if cdepth == 0:
                    mode = st['after_comment']
                continue
            out.append(('k', depth))
            i += 1
            continue
        if mode == 's':
            if c == '\\' and i + 1 < n:
                out += [('s', depth)] * 2
                i += 2
                continue
            out.append(('s', depth))
            if c == '"':
                mode = st['after_string']
            i += 1
            continue
        if mode == 'q':
            if c == '`':
                out.append(('q', depth))
                mode = 'c'
                i += 1
                continue
            if c == '"':
                st['after_string'] = 'q'
                mode = 's'
                out.append(('s', depth))
                i += 1
                continue
            if c in '([{':
                out.append(('q', depth))
                depth += 1
                i += 1
                continue
            if c in ')]}':
                depth -= 1
                out.append(('q', depth))
                i += 1
                continue
            out.append(('q', depth))
            i += 1
            continue
        if two == '(*':
            st['after_comment'] = 'c'
            mode = 'k'
            cdepth = 1
            out += [('k', depth)] * 2
            i += 2
            continue
        if c == '"':
            st['after_string'] = 'c'
            mode = 's'
            out.append(('s', depth))
            i += 1
            continue
        if c == '`':
            out.append(('q', depth))
            mode = 'q'
            i += 1
            continue
        prev_ident = i > 0 and (line[i-1].isalnum() or line[i-1] in "_'")
        if c == "'" and not prev_ident and i + 2 < n and line[i+2] == "'":
            out += [('s', depth)] * 3
            i += 3
            continue
        if (c == "'" and not prev_ident and i + 3 < n
                and line[i+1] == '\\' and line[i+3] == "'"):
            out += [('s', depth)] * 4
            i += 4
            continue
        if c in '([{':
            out.append(('c', depth))
            depth += 1
            i += 1
            continue
        if c in ')]}':
            depth -= 1
            out.append(('c', depth))
            i += 1
            continue
        out.append(('c', depth))
        i += 1
    st['mode'] = mode
    st['cdepth'] = cdepth
    return out, st


def new_state():
    return {'mode': 'c', 'cdepth': 0, 'after_comment': 'c',
            'after_string': 'c'}


def tokens(text):
    """code tokens (comments removed, whitespace ignored, strings and char
    literals as single tokens)"""
    toks = []
    st = new_state()
    for line in text.split('\n'):
        states, st = scan(line, st)
        i = 0
        n = len(line)
        while i < n:
            m = states[i][0]
            if m == 'k' or line[i] in ' \t':
                i += 1
                continue
            if m == 's':
                j = i
                while j < n and states[j][0] == 's':
                    j += 1
                toks.append(line[i:j])
                i = j
                continue
            mt = TOKEN.match(line, i)
            toks.append(mt.group(0))
            i = mt.end()
    return toks


def comment_words(text):
    """words inside comments, ignoring the (* *) delimiters (re-wrapping a
    comment moves them); rulers of - or = may be shortened"""
    words = []
    st = new_state()
    cur = ''
    for line in text.split('\n'):
        states, st = scan(line, st)
        for ch, (m, d) in zip(line, states):
            if m == 'k' and ch not in ' \t':
                cur += ch
            elif cur:
                words.append(cur)
                cur = ''
        if cur:
            words.append(cur)
            cur = ''
    out = []
    for w in words:
        for w2 in w.replace('(*', ' ').replace('*)', ' ').split():
            if len(w2) > 3 and set(w2) <= set('-='):
                out.append(w2[0])
            else:
                out.append(w2)
    return out


# ---------------------------------------------------------------------------
def indent_of(line):
    return len(line) - len(line.lstrip(' '))


def wrap_comment_line(line, width):
    ind = indent_of(line)
    body = line.strip()
    if not (body.startswith('(*') and body.endswith('*)')):
        return None
    if body.count('(*') != 1 or body.count('*)') != 1:
        return None
    inner = body[2:-2]
    banner = (len(line) >= width - 1
              and len(inner) - len(inner.rstrip()) >= 2)
    text = inner.strip()
    if not text:
        return [' ' * ind + '(*' + ' ' * (width - ind - 4) + '*)']
    if set(text) <= set('-='):
        return [' ' * ind + '(* ' + text[0] * (width - ind - 6) + ' *)']
    avail = width - ind - 6
    lines, cur = [], ''
    for w in text.split(' '):
        if not w:
            continue
        if not cur:
            cur = w
        elif len(cur) + 1 + len(w) <= avail:
            cur += ' ' + w
        else:
            lines.append(cur)
            cur = w
    if cur:
        lines.append(cur)
    out = [' ' * ind + '(* ' + (l.ljust(avail) if banner else l) + ' *)'
           for l in lines]
    if any(len(l) > width for l in out):
        return None
    return out


def candidates(line, states, width):
    """break candidates: (priority, pos, cont_indent, tail_len); pos = index
    where the rest starts (after the boundary and any spaces); the head is
    line[:pos].rstrip()"""
    n = len(line)
    ind = indent_of(line)
    cands = []
    # innermost open bracket index before each position
    opens = []
    open_at = [None] * (n + 1)
    for i in range(n):
        open_at[i] = opens[-1] if opens else None
        m, d = states[i]
        if m in ('c', 'q'):
            if line[i] in '([{':
                opens.append(i)
            elif line[i] in ')]}' and opens:
                opens.pop()
    open_at[n] = opens[-1] if opens else None
    first_q = line.find('`')
    starts_with_q = line.lstrip(' ').startswith('`')
    bounds = []                       # (pos_after_boundary, kind)
    for i in range(ind + 1, n):
        m, d = states[i]
        pm = states[i-1][0]
        if m == 's':
            if line[i-1] in ';,' and pm in ('c', 'q'):
                bounds.append((i, 'sep'))
            continue
        if m == 'k':
            if (line[i] == ' ' and line[i-1] != ' ' and pm == 'k'
                    and line[i-2:i] != '(*'):
                bounds.append((i, 'cspace'))
            continue
        if line[i] == ' ' and line[i-1] != ' ':
            bounds.append((i, 'space'))
        elif line[i-1] in ';,' and line[i] not in ' ;,' and pm in ('c', 'q'):
            bounds.append((i, 'sep'))
        elif line[i] == '`' and m == 'q' and line[i-1] != ' ' and pm == 'c':
            bounds.append((i, 'qopen'))
        elif line[i-1] == '`' and pm == 'q' and m == 'c' and line[i] != ' ':
            bounds.append((i, 'qclose'))
        elif (m == 'q' and (line[i:i+2] == '->' or line[i] == '#')
                and line[i-1] not in ' -#'):
            bounds.append((i, 'arrow'))
    if not bounds:
        return []
    valid = [(p, k) for p, k in bounds if len(line[:p].rstrip()) <= width]
    if not valid:
        return []
    mind = min(states[p][1] for p, k in valid)
    for p, kind in valid:
        head = line[:p].rstrip()
        rest = line[p:].lstrip(' ')
        if not head.strip() or not rest:
            continue
        m, d = states[p]
        ob = open_at[p]
        if kind == 'arrow':
            if ob is not None and ob + 1 < width - 25:
                cont = ob + 1
            else:
                cont = ind + 4
            cands.append((7.5, p, cont, len(line) - p))
            continue
        if kind == 'cspace':
            cstart = line.find('(*')
            cont = (cstart + 3) if cstart >= 0 else ind
            cands.append((8, p, cont, len(line) - p))
            continue
        hm = states[len(head) - 1][0]           # mode of the last head char
        last = re.search(r"(\S+)$", head).group(1)
        nxt = re.match(r"\S+", rest).group(0)
        # continuation indentation
        if ob is not None and d > mind:
            cont = ob + 1
        elif m == 'q' and starts_with_q and first_q >= 0:
            cont = first_q + 1
        elif m == 'q':
            cont = ind
        else:
            cont = ind + 2
        tail = len(rest)
        if d == mind:
            if hm == 'c' and last in ('THEN', 'THENL', 'ORELSE'):
                cands.append((0, p, ind, tail))
            elif last.endswith(';') and ob is not None:
                cands.append((1, p, ob + 1, tail))
            elif last.endswith(';'):
                cands.append((1, p, ind, tail))
            elif kind == 'qclose' or (last.endswith('`') and m == 'c'):
                cands.append((2, p, ind, tail))
            elif kind == 'qopen' or (nxt.startswith('`') and hm == 'c'):
                cands.append((2.2, p, ind + 2, tail))
            elif nxt.startswith('(*'):
                cands.append((2, p, ind, tail))
            elif nxt in ('else', 'and') or last in ('in', 'with'):
                cands.append((3.05, p, cont if m == 'q' else ind, tail))
            elif nxt == 'then':
                cands.append((3.15, p, cont if m == 'q' else ind, tail))
            elif last in OP_RANK and m == 'q':
                cands.append((3.2 + OP_RANK[last] / 10, p, cont, tail))
            elif last.endswith(','):
                cands.append((3.65, p, cont, tail))
            else:
                cands.append((4, p, cont, tail))
            continue
        if last.endswith(';') and ob is not None:
            cands.append((5, p, ob + 1, tail))
        elif ob is not None and ob + 1 < width - 25:
            cands.append((6, p, ob + 1, tail))
        else:
            cands.append((7, p, ind + 4, tail))
    return cands


def choose(cands, line, width):
    if not cands:
        return None

    def key(c):
        pr, p, cont, tail = c
        penalty = 0
        if tail < 12:                             # avoid tiny tails
            penalty += 2
        if len(line[:p].rstrip().strip()) < 12:   # and tiny heads
            penalty += 2
        if cont + tail > width and cont + tail >= len(line):
            penalty += 1                          # no progress
        return (pr + penalty, -p)

    best = min(cands, key=key)
    pr, p, cont, tail = best
    if cont + tail > width:
        cont = max(1, min(cont, width - tail))
    if cont + tail >= len(line):
        cont = indent_of(line) + 2
    return p, cont


def wrap_in_comment(cur, width):
    """word wrap of a line that starts inside a multi-line comment"""
    ind = indent_of(cur)
    best = None
    for i in range(ind + 1, min(len(cur), width + 1)):
        if cur[i] == ' ' and cur[i-1] != ' ':
            best = i
    if best is None:
        return None
    return cur[:best].rstrip(), ' ' * ind + cur[best:].lstrip(' ')


def reflow_file(text, width=WIDTH):
    out = []
    report = []
    st = new_state()
    for ln, line in enumerate(text.split('\n'), 1):
        line = line.rstrip(' ')
        if len(line) <= width:
            _, st = scan(line, st)
            out.append(line)
            continue
        if st['mode'] == 'c' and line.strip().startswith('(*'):
            w = wrap_comment_line(line, width)
            if w is not None:
                for l in w:
                    _, st = scan(l, st)
                out.extend(w)
                continue
        cur = line
        pieces = []
        st_line = dict(st)
        while len(cur) > width:
            states, _ = scan(cur, dict(st_line))
            if st_line['mode'] == 'k':
                w = wrap_in_comment(cur, width)
                if w is None:
                    break
                pieces.append(w[0])
                cur = w[1]
                continue
            b = choose(candidates(cur, states, width), cur, width)
            if b is None:
                break
            p, cont = b
            head = cur[:p].rstrip()
            rest = cur[p:].lstrip(' ')
            pieces.append(head)
            _, st_line = scan(head, st_line)
            cur = ' ' * cont + rest
        pieces.append(cur)
        if len(cur) > width:
            report.append((ln, len(cur), cur.strip()[:60]))
        for p in pieces:
            _, st = scan(p, st)
        out.extend(pieces)
    return '\n'.join(out), report


ASCII_MAP = {'\u2014': '--', '\u2013': '-', '\u2260': '<>', '\u2264': '<=',
             '\u2265': '>=', '\u03b4': 'd', '\u2286': 'SUBSET',
             '\U0001d7d9': 'ind', '\u2018': "'", '\u2019': "'",
             '\u201c': '"', '\u201d': '"', '\u2026': '...', '\u00d7': 'x',
             '\u2212': '-', '\u2192': '->', '\u2208': 'IN', '\u00f6': 'oe',
             '\u00e9': 'e', '\u00a0': ' '}


def to_ascii(text):
    out = []
    unknown = set()
    for ch in text:
        if ord(ch) < 128:
            out.append(ch)
        elif ch in ASCII_MAP:
            out.append(ASCII_MAP[ch])
        else:
            unknown.add(ch)
            out.append(ch)
    return ''.join(out), unknown


def main():
    args = sys.argv[1:]
    apply = '--apply' in args
    ascii_ = '--ascii' in args
    width = WIDTH
    if '--width' in args:
        k = args.index('--width')
        width = int(args[k + 1])
        del args[k:k+2]
    files = [a for a in args if a not in ('--apply', '--ascii')]
    total_long = total_left = 0
    bad = []
    for f in files:
        text = open(f).read()
        if ascii_:
            text2, unknown = to_ascii(text)
            if unknown:
                print(f'{f}: UNMAPPED non-ASCII characters {sorted(unknown)}')
            if text2 != text:
                k = sum(1 for c in text if ord(c) > 127)
                print(f'{f}: {k} non-ASCII characters replaced')
                text = text2
        nlong = sum(1 for l in text.split('\n') if len(l.rstrip(' ')) > width)
        if nlong == 0:
            if apply and ascii_ and text != open(f).read():
                open(f, 'w').write(text)
            continue
        new, report = reflow_file(text, width)
        ok = (tokens(text) == tokens(new)
              and comment_words(text) == comment_words(new))
        left = sum(1 for l in new.split('\n') if len(l) > width)
        total_long += nlong
        total_left += left
        verdict = 'IDENTICAL' if ok else 'DIFFER !!!'
        print(f'{f}: {nlong} long -> {left} left; {len(text.splitlines())}'
              f' -> {len(new.splitlines())} lines; tokens {verdict}')
        for ln, l, s in report[:4]:
            print(f'    unfixable line {ln} ({l} cols): {s}')
        if not ok:
            bad.append(f)
        if apply and ok:
            open(f, 'w').write(new)
    summary = f'TOTAL: {total_long} long lines, {total_left} left'
    if bad:
        summary += f'; TOKEN MISMATCH in {bad}'
    print(summary)


if __name__ == '__main__':
    main()
