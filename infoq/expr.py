"""infoq.expr -- 信息表达式解析。

把 I(X;Y|Z)、H(X|Y)、H(X,Y) 等信息量表达式解析为 h(S) 的线性组合，
其中 h(S) := H(X_S) 是变量子集 S 的联合熵（h(空集)=0，永不存储）。

线性形式（linear form）用 dict 表示：{frozenset(变量名): Fraction}，
代表  sum_S c_S * H(X_S)。全部系数用精确有理数运算。
"""
from __future__ import annotations

from fractions import Fraction
import re

__all__ = ["ExprError", "parse", "parse_claim", "parse_constraint", "pretty"]


class ExprError(ValueError):
    """表达式语法错误。"""


_TOKEN_RE = re.compile(
    r"\s*(?:(?P<num>\d+(?:\.\d+)?(?:/\d+(?:\.\d+)?)?)"
    r"|(?P<name>[A-Za-z_]\w*)"
    r"|(?P<sym>[()+\-;|,=<>*]))"
)
_RESERVED = {"H", "I"}
_CLAIM_RE = re.compile(r"(<=|>=|<|>|=)")
_CHAIN_RE = re.compile(r"^\s*[A-Za-z_]\w*(?:\s*-\s*[A-Za-z_]\w*)+\s*$")


def _tokenize(s: str):
    tokens = []
    pos = 0
    while pos < len(s):
        m = _TOKEN_RE.match(s, pos)
        if m is None:
            rest = s[pos:].strip()
            if not rest:
                break
            raise ExprError(f"无法识别的字符 {rest[0]!r}（位置 {pos}）：{s!r}")
        if m.lastgroup == "num":
            tokens.append(("num", m.group("num")))
        elif m.lastgroup == "name":
            tokens.append(("name", m.group("name")))
        else:
            tokens.append(("sym", m.group("sym")))
        pos = m.end()
    return tokens


def _frac(s: str) -> Fraction:
    if "." in s or "/" in s:
        return Fraction(s)
    return Fraction(int(s))


def _add(a: dict, b: dict) -> dict:
    out = dict(a)
    for k, v in b.items():
        nv = out.get(k, Fraction(0)) + v
        if nv == 0:
            out.pop(k, None)
        else:
            out[k] = nv
    return out


def _scale(a: dict, c: Fraction) -> dict:
    if c == 0:
        return {}
    return {k: v * c for k, v in a.items()}


def _fmt_set(S) -> str:
    return ",".join(sorted(S))


class _Parser:
    def __init__(self, tokens, src):
        self.toks = tokens
        self.i = 0
        self.src = src

    def _peek(self):
        if self.i < len(self.toks):
            return self.toks[self.i]
        return (None, None)

    def _next(self):
        tok = self._peek()
        self.i += 1
        return tok

    def _expect(self, kind, val=None):
        k, v = self._next()
        if k != kind or (val is not None and v != val):
            want = val if val is not None else kind
            raise ExprError(f"期望 {want!r}，但遇到 {v!r}：{self.src!r}")
        return v

    def parse_expr(self) -> dict:
        sign = Fraction(1)
        while True:
            k, v = self._peek()
            if k == "sym" and v in "+-":
                self._next()
                if v == "-":
                    sign = -sign
            else:
                break
        form = self._parse_term(sign)
        while True:
            k, v = self._peek()
            if k == "sym" and v in "+-":
                self._next()
                form = _add(form, self._parse_term(Fraction(1) if v == "+" else Fraction(-1)))
            else:
                break
        return form

    def _parse_term(self, sign: Fraction) -> dict:
        k, v = self._peek()
        if k == "num":
            self._next()
            k2, v2 = self._peek()
            starts_atom = (k2 == "name" and v2 in _RESERVED) or (k2 == "sym" and v2 == "(")
            if not starts_atom:
                # 独立常数：信息量是齐次线性组合，只允许常数 0
                if _frac(v) != 0:
                    raise ExprError(
                        f"非零常数项 {v} 无意义（信息不等式只能是信息量的线性组合）：{self.src!r}")
                return {}
            coef = _frac(v) * sign
            if k2 == "sym" and v2 == "(":
                self._next()
            return _scale(self._parse_primary(), coef)
        return _scale(self._parse_primary(), sign)

    def _parse_primary(self) -> dict:
        k, v = self._peek()
        if k == "sym" and v == "(":
            self._next()
            form = self.parse_expr()
            self._expect("sym", ")")
            return form
        if k == "name" and v in _RESERVED:
            return self._parse_atom()
        raise ExprError(f"期望表达式原子（H(...) / I(...) / 括号组），遇到 {v!r}：{self.src!r}")

    def _parse_union(self) -> frozenset:
        names = []
        while True:
            k, v = self._next()
            if k != "name":
                raise ExprError(f"期望变量名，遇到 {v!r}：{self.src!r}")
            if v in _RESERVED:
                raise ExprError(f"{v!r} 是保留字（H/I），不能作变量名：{self.src!r}")
            if v not in names:
                names.append(v)
            k2, v2 = self._peek()
            if k2 == "sym" and v2 == ",":
                self._next()
                continue
            break
        return frozenset(names)

    def _parse_atom(self) -> dict:
        fname = self._expect("name")
        self._expect("sym", "(")
        A = self._parse_union()
        if fname == "H":
            T = frozenset()
            k, v = self._peek()
            if k == "sym" and v == "|":
                self._next()
                T = self._parse_union()
            self._expect("sym", ")")
            form = {A | T: Fraction(1)}
            if T:
                form = _add(form, {T: Fraction(-1)})   # H(A|T) = h(A∪T) - h(T)
            return form
        if fname == "I":
            self._expect("sym", ";")
            B = self._parse_union()
            C = frozenset()
            k, v = self._peek()
            if k == "sym" and v == "|":
                self._next()
                C = self._parse_union()
            self._expect("sym", ")")
            # I(A;B|C) = h(A∪C) + h(B∪C) - h(A∪B∪C) - h(C)
            form = {A | C: Fraction(1), B | C: Fraction(1), A | B | C: Fraction(-1)}
            if C:
                form = _add(form, {C: Fraction(-1)})
            return form
        raise ExprError(f"未知的函数 {fname!r}：{self.src!r}")


def parse(s: str) -> dict:
    """把信息量线性组合解析为 {frozenset: Fraction} 线性形式。

    例：parse("2*I(X;Y) - H(X|Z)")  →  h(X)+h(Y)-h(XY)+h(Z)-h(XZ) 的系数字典。
    """
    toks = _tokenize(s)
    if not toks:
        raise ExprError("空表达式")
    p = _Parser(toks, s)
    form = p.parse_expr()
    if p.i != len(toks):
        k, v = p._peek()
        raise ExprError(f"多余的输入 {v!r}：{s!r}")
    return form


def parse_claim(s: str):
    """解析不等式/等式命题，返回 (op, lhs_str, rhs_str, lhs_form, rhs_form)。"""
    m = _CLAIM_RE.search(s)
    if not m:
        raise ExprError(f"缺少比较符（>=、<=、= 等）：{s!r}")
    op = m.group(0)
    lhs_str = s[: m.start()].strip()
    rhs_str = s[m.end():].strip()
    return op, lhs_str, rhs_str, parse(lhs_str), parse(rhs_str)


def parse_constraint(s: str) -> list:
    """把约束解析为一组等于 0 的线性形式。

    支持两种写法：
      "X-Y-Z"        马尔可夫链，展开为全部成对条件独立约束
      "I(X;Z|Y) = 0" 一般等式约束
    """
    if _CHAIN_RE.match(s):
        names = [t.strip() for t in s.split("-")]
        forms = []
        for i in range(len(names)):
            for j in range(i + 2, len(names)):
                mid = ",".join(names[i + 1: j])
                forms.append(parse(f"I({names[i]};{names[j]}|{mid})"))
        return forms
    if "=" in s:
        lhs, rhs = s.split("=", 1)
        return [_add(parse(lhs), _scale(parse(rhs), Fraction(-1)))]
    raise ExprError(f"约束须为马尔可夫链 'A-B-C' 或 '表达式 = 0' 形式：{s!r}")


def pretty(form: dict) -> str:
    """把线性形式打印回可读表达式（h(S) 均写成 H(变量名,...) 形式）。"""
    if not form:
        return "0"
    items = sorted(form.items(), key=lambda kv: (len(kv[0]), sorted(kv[0])))
    terms = []
    for S, c in items:
        st = f"H({_fmt_set(S)})"
        if c == 1:
            terms.append(st)
        elif c == -1:
            terms.append(f"-{st}")
        else:
            terms.append(f"{c}*{st}")
    out = terms[0]
    for t in terms[1:]:
        out += f" + {t}" if not t.startswith("-") else f" - {t[1:]}"
    return out
