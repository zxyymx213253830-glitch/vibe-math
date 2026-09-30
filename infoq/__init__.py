"""infoq -- 信息论研究的机检工作流。

组件：
  expr       信息表达式解析（I(X;Y|Z) → h(S) 线性形式）
  shannon_lp Shannon 型不等式 LP 判定器（ITIP 数学内核的自研实现，含精确证书）
  numeric    数值反例预言机（随机采样 + 局部精修找反例/紧性）
  converse   converse 证明逐步机检
"""
from .expr import ExprError, parse, parse_claim, parse_constraint, pretty
from .numeric import Oracle
from .shannon_lp import (NOT_IDENTIFIED, PROVED, SOLVER_ERROR, UNVERIFIED,
                         ShannonResult, check)
from .converse import check_steps, format_report

__version__ = "0.2.0"

__all__ = [
    "ExprError", "parse", "parse_claim", "parse_constraint", "pretty",
    "Oracle", "ShannonResult", "check", "PROVED", "NOT_IDENTIFIED",
    "UNVERIFIED", "SOLVER_ERROR",
    "check_steps", "format_report", "__version__",
]
