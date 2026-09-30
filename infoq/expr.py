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
    r"|(?P<sym>[()+\-;|,=<>*/]))"
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
    try:
        if "." in s or "/" in s:
            return Fraction(s)
        return Fraction(int(s))
    except ZeroDivisionError:
        raise ExprError(f"除数不能为 0：{s!r}") from None
    except ValueError:
        raise ExprError(f"无法解析为有理数：{s!r}") from None


def _fold_scalar(toks, src: str) -> Fraction:
    """把只含数字与 '*' '/' 的 token 序列折叠成一个有理数。

    调用方需先保证 token 序列只含 num 与 '*' '/'（见 `_Parser._paren_is_scalar`）。
    """
    val = Fraction(1)
    op = "*"
    for k, v in toks:
        if k == "num":
            f = _frac(v)
            try:
                val = val * f if op == "*" else val / f
            except ZeroDivisionError:
                raise ExprError(f"除数不能为 0：{src!r}") from None
        elif k == "sym" and v in "*/":
            op = v
        else:  # pragma: no cover - 由调用方保证不会发生
            raise ExprError(f"标量中出现非数字符号 {v!r}：{src!r}")
    return val


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

    def _matching_paren(self, open_idx: int) -> int:
        """open_idx 处 '(' 对应 ')' 的 token 下标；不匹配时返回 -1。"""
        depth = 0
        for j in range(open_idx, len(self.toks)):
            k, v = self.toks[j]
            if k == "sym" and v == "(":
                depth += 1
            elif k == "sym" and v == ")":
                depth -= 1
                if depth == 0:
                    return j
        return -1

    def _paren_is_scalar(self, open_idx: int) -> bool:
        """括号内是否只含数字与 '*' '/'（即一个纯标量，如 "(1/3)"）。"""
        j = self._matching_paren(open_idx)
        if j < 0:
            return False
        return all(k == "num" or (k == "sym" and v in "*/")
                   for k, v in self.toks[open_idx + 1:j])

    def _parse_term(self, sign: Fraction) -> dict:
        """解析一个乘法项：若干标量（数字，可含 `/`）与至多一个信息量原子相乘。

        合法形式（标量倍乘，`*` 可省略）：
            2*I(X;Y)    3/2*H(X,Y,Z)    2*(H(X)+H(Y))    2 I(X;Y)
            I(X;Y)*2    2*3*I(X;Y)      2 / 3 * I(X;Y)    (1/3)*H(X)
        不合法：
            H(X)*H(Y)   —— 信息量之间不能相乘，结果不再是信息量的线性组合
            2           —— 非零常数项无意义
            2**I(X;Y)   —— 连续的 '*' 无意义
        """
        coef = Fraction(1)
        form: dict | None = None
        consumed = 0
        pending_star = False
        # "(1/3)*H(X)"：项首的纯标量括号组先吸收成系数
        if (self.i < len(self.toks) and self.toks[self.i] == ("sym", "(")
                and self._paren_is_scalar(self.i)):
            close = self._matching_paren(self.i)
            coef = _fold_scalar(self.toks[self.i + 1:close], self.src)
            self.i = close + 1
            consumed += 1
            k2, v2 = self._peek()
            if k2 == "sym" and v2 == "*":
                self._next()
                consumed += 1
                pending_star = True
        while True:
            k, v = self._peek()
            if k == "num":
                self._next()
                consumed += 1
                pending_star = False
                f = _frac(v)
                k2, v2 = self._peek()
                if k2 == "sym" and v2 == "/":
                    # 词法器已把无空格的 "3/2" 合成一个 num；这里处理 "3 / 2" 的写法
                    self._next()
                    k3, v3 = self._next()
                    if k3 != "num":
                        raise ExprError(f"'/' 后期望数字，遇到 {v3!r}：{self.src!r}")
                    consumed += 1
                    f = f / _frac(v3)
                coef *= f
                k2, v2 = self._peek()
                if k2 == "sym" and v2 == "*":
                    self._next()
                    consumed += 1
                    pending_star = True
                    continue
                # 隐式乘法：数字后面直接跟原子（如 "2 I(X;Y)"）
                if ((k2 == "name" and v2 in _RESERVED)
                        or (k2 == "sym" and v2 == "(") or k2 == "num"):
                    continue
                break
            if (k == "name" and v in _RESERVED) or (k == "sym" and v == "("):
                atom = self._parse_primary()
                consumed += 1
                pending_star = False
                if form is None:
                    form = atom
                else:
                    raise ExprError(
                        "信息量之间不能用 '*' 相乘（'*' 仅表示标量倍乘）："
                        f"{self.src!r}")
                k2, v2 = self._peek()
                if k2 == "sym" and v2 == "*":
                    self._next()
                    consumed += 1
                    pending_star = True
                    continue
                break
            if k == "sym" and v == "*":
                if consumed == 0 or pending_star:
                    break          # 项首或连续的 '*' 交由上方统一报错
                self._next()
                consumed += 1
                pending_star = True
                continue
            break

        if pending_star:
            raise ExprError(f"'*' 后期望信息量或数字：{self.src!r}")
        if consumed == 0:
            k, v = self._peek()
            raise ExprError(
                f"期望表达式原子（H(...) / I(...) / 括号组），遇到 {v!r}：{self.src!r}")

        if form is None:
            # 纯标量项：信息量是齐次线性组合，只允许常数 0
            if coef != 0:
                raise ExprError(
                    f"非零常数项 {coef} 无意义（信息不等式只能是信息量的线性组合）："
                    f"{self.src!r}")
            return {}
        return _scale(form, coef * sign)

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

    支持标量倍乘（`*` 可省略）与分数系数：
        parse("2*I(X;Y)")            →  h(X)+h(Y)-h(XY) 的 2 倍
        parse("3/2*H(X,Y,Z)")        →  h(X,Y,Z) 的 3/2 倍
        parse("2*I(X;Y) - H(X|Z)")   →  混合线性组合
        parse("2*(H(X)+H(Y))")       →  括号组
        parse("I(X;Y)*2")            →  反向书写同样合法

    不允许信息量之间相乘（`H(X)*H(Y)`），那不再是信息量的线性组合；
    也不允许非零常数项。
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
