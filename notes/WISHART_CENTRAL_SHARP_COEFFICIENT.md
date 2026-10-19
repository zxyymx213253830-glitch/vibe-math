# Central minimum: a finite sharp hard-edge coefficient

Research supplement2026-10-19, proof bodies Codex. Not a revision of the frozen
manuscript. [需人工审查] Measure/Fubini/variance/spectral notation correspondence.

Let N>0, m=N+d, d>=0, and Z be the actual matrix of independent CN(0,1) entries,
with real/imaginary variance1/2. Let F be the CDF of the least eigenvalue of Z^H Z.
Existing source-space probability proofs give, for x>=0,

    F(x)=1-exp(-N*x)*P(x)/M,

where P is the fixed real polynomial obtained by applying the finite Gaussian
factorial functional to det(W+xI)^d for an N by N actual square complex sample.
M=E[det(W)^d] is the already proved positive finite product of factorial ratios;
P(0)=M. Neither P nor M is an assumed target density. No probability integral is
left in their coefficient definitions.

Set k=d+1. The new checked statement is

    lim_(x->0+) F(x)/x^k = a > 0,

with the exact finite expression

    a = -1/(M*k!) * SUM_(i=0..k) choose(k,i)*(-N)^i*(k-i)!*[x^(k-i)]P(x).

All subtractions in the sum have i<=k. In Lean the sum uses range(k+1), and the
polynomial parameter n=N-1 where applicable. The simpler candidate factorial
constant m!/((N-1)!*(d+1)!^2) is checked only in the symbolic control's scalar
Gamma and N=2,d=0..4 cases. Its GENERAL equality to a is NOT formalized here.
This note does not establish the original general paper T4 normalization.

The proof avoids an important invalid shortcut: a log exponent by itself need
not give a sharp ratio limit. It uses the analytic continuation
G(x)=1-exp(-N*x)*P(x)/M on ALL real x. The actual CDF is piecewise zero for x<0;
it is not assumed analytic across0.

1. Existing actual lower/upper power bounds give positive F on a right interval
   and log F(x)/log x ->k.
2. The continuation G agrees with F for x>=0 and is analytic at0. Positivity
   prevents an identically zero germ. Locked mathlib isolated-zero factorization
   gives G=x^j H locally with H analytic and H(0)!=0.
3. Right positivity and continuity imply H(0)>0. Bounding H between H(0)/2 and
   2H(0) gives log G/log x ->j. Uniqueness of limits identifies j=k.
4. Analytic-order/Taylor APIs show all derivatives belowk vanish, and
   a=iteratedDeriv k G0/k!>0. An analytic remainder, not merely formal series
   manipulation, proves the ratio limit.
5. Polynomial/calculus derivative agreement and Leibniz's rule remove the
   derivative, giving the finite sum above.

Source modules: AnalyticPositivePowerLimit, AnalyticPowerTaylorCoefficient,
CentralMinimumSharpOrder, CentralMinimumHardEdgeCoefficient,
ExponentialPolynomialTaylor, CentralMinimumFiniteHardEdgeCoefficient.
The generic lemmas apply to positive analytic germs with a finite integer log
exponent. They do not assert a factorization theorem for arbitrary smooth
nonanalytic functions. No uniformity as d,N vary is needed or claimed.

The symbolic control reads the independent prior finite-factorial coefficient
control, compares the sum against direct SymPy expansion of1-exp(-2x)Q, and
checks scalar Gamma cases. These controls are not proof dependencies and not
evidence that finitely many parameter cases cover all shapes.

The actual ONE-dimensional minimum density is now also proved, with respect
to ordinary Lebesgue measure: exp(-N*x)/M*(N*P(x)-P'(x)) forx>0 and0 forx<=0.
The proof reconstructs a measure from its independently proved CDF using
Measure.ext_of_Iic and FTC on finite intervals. Nonnegativity is derived from
monotonicity of the actual CDF; ofReal does not silently discard negative mass.
Mass1, mathlib HasPDF and canonical RN-pdf AE equality are checked separately.
This is NOT the joint spectral density G2 or a general noncentral explicit PDF.
