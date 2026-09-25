import Mathlib

/- Local toolchain / Mathlib smoke test only.
   This deliberately does not import the upstream GPL-3.0-only package. -/

example (z : ℂ) : Complex.normSq z = Complex.normSq z := rfl

