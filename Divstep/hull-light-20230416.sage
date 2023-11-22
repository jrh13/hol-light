#!/usr/bin/env sage

# general improvements to consider:
# * take more advantage of +- symmetry
# * shorter addition chains for monomials()
# * factor out more lemmas
# * reduce precision for intermediate results
# * the 32/33 doesn't seem to help; skipping would remove some cases
# * initialsteps>0 doesn't seem to help; remove portions of code using it
# * narrow the lattice-point logic to just considering the odd-f cases (if this helps)
# * build lemmas to merge local note-note patterns

import sys

approx = True
if len(sys.argv) > 1 and sys.argv[1] == 'exact':
  approx = False

try:
  from collections.abc import Hashable
except:
  from collections import Hashable

class memoized(object):
  def __init__(self,func):
    self.func = func
    self.cache = {}
    self.__doc__ = '   [memoized.memoized wrapper around the following:]\n'
    if func.__doc__ != None:
      self.__doc__ += func.__doc__
    self.__wrapped__ = func
  def __call__(self,*args):
    if not isinstance(args,Hashable):
      return self.func(*args)
    if not args in self.cache:
      self.cache[args] = self.func(*args)
    return self.cache[args]

proof.all(False)

UP0 = matrix([[1,0],[0,1/2]])
UP1 = matrix([[1,0],[1/2,1/2]])
DOWN = matrix([[0,1],[-1/2,1/2]])

@memoized
def RI(bits):
  return RealIntervalField(bits)
  
if approx:
  s = 30902639/41749730

  QQxy.<y> = PolynomialRing(QQ,sparse=True)

  def QQxy_from_L(x):
    return x

  def Lsign(x):
    return sign(x)

  def LtoRR(x):
    return RR(x)

  def Lmax(v):
    return max(v)

  def Lmaxpos(v):
    vmax = max(v)
    return [j for (j,vj) in enumerate(v) if vj == vmax]

else:
  QQx.<x> = PolynomialRing(QQ,sparse=True)
  Delta = 273548757304312537
  qpoly = x^2-Delta
  hol_qpoly = 'q pow 2 - &%d' % Delta
  K.<q> = NumberField(qpoly)
  
  QQxy.<y> = PolynomialRing(QQx,sparse=True)
  spoly = y^54-(1591853137+3*x)/2^55
  hol_spoly = 's pow 54 - (&1591853137 + &3 * q) / &2 pow 55'
  Kz.<z> = K[]
  L.<s> = NumberField(spoly(z,q))

  @memoized
  def RI_q(bits):
    return sqrt(RI(bits)(Delta))
  
  @memoized
  def RI_q_pow(bits,n):
    return RI_q(bits)^n
  
  @memoized
  def RI_s(bits):
    return ((1591853137+3*RI_q(bits))/2^55)^(1/54)
  
  @memoized
  def RI_s_pow(bits,n):
    return RI_s(bits)^n
  
  @memoized
  def Lsparse(beta):
    beta = L(beta)
    result = []
    for j,betaj in enumerate(beta):
      for k,betajk in enumerate(betaj):
        if betajk == 0: continue
        result += [(j,k,betajk)]
    return result
  
  @memoized
  def QQxysparse(P):
    P = QQxy(P)
    result = []
    for j,Pj in enumerate(P):
      for k,Pjk in enumerate(Pj):
        if Pjk == 0: continue
        result += [(j,k,Pjk)]
    return result
  
  def Lsign(beta):
    beta = L(beta)
    sparse = Lsparse(beta)
    if len(sparse) == 0: return 0
    if all(betajk > 0 for j,k,betajk in sparse):
      return 1
    if all(betajk < 0 for j,k,betajk in sparse):
      return -1
  
    bits = 8
    while True:
      result = sum(betajk*RI_s_pow(bits,j)*RI_q_pow(bits,k) for j,k,betajk in sparse)
      if result > 0:
        return 1
      if result < 0:
        return -1
      bits *= 2
  
  RR = RealField(64)
  for phi in L.embeddings(RR):
    if phi(s) > 0:
      if phi((s^54)*2^55-1591853137) > 0:
        LtoRR = phi
  
  def Lmaxpos(betalist):
    ratings = [LtoRR(beta) for beta in betalist]
    ratingsmax = max(ratings)
    result = [i for i in range(len(ratings)) if ratings[i] == ratingsmax]
  
    check = False
    if check:
      # XXX: can handle failure here by doubling RR precision and retrying
      for j,betaj in enumerate(betalist):
        if j in result:
          assert betaj == betalist[result[0]]
        else:
          assert Lsign(betalist[result[0]]-betaj) >= 0
  
    return result
  
  def Lmax(betalist):
    return betalist[Lmaxpos(betalist)[0]]

def hol_topmatter():
  return r'''(* ----- tactics *)

let def n d = X_CHOOSE_TAC n(MESON [] (mk_exists (n, mk_eq (n, d))));;

let notetac t tac = SUBGOAL_THEN t MP_TAC THENL
[tac;
  ALL_TAC] THEN
DISCH_THEN(fun th -> ASSUME_TAC th);;

let note t why = notetac t(ASM_MESON_TAC why);;

let choosevar n p why = note(mk_exists (n, p)) why THEN
X_CHOOSE_TAC n(UNDISCH (TAUT (mk_imp (mk_exists (n, p), mk_exists (n, p)))));;

let num_linear t = ASSUME_TAC(UNDISCH_ALL (REWRITE_RULE [IMP_CONJ] (ARITH_RULE t)));;

let int_linear t = ASSUME_TAC(UNDISCH_ALL (REWRITE_RULE [IMP_CONJ] (INT_ARITH t)));;

let real_linear t = ASSUME_TAC(UNDISCH_ALL (REWRITE_RULE [IMP_CONJ] (REAL_ARITH t)));;

let real_cancel t = ASSUME_TAC(UNDISCH_ALL (REWRITE_RULE [IMP_CONJ] (REAL_FIELD t)));;

let specialize v th = ASSUME_TAC(UNDISCH_ALL (REWRITE_RULE [IMP_CONJ] (ISPECL v th)));;

let twocases c why = note c why THEN
DISJ_CASES_TAC(UNDISCH(ITAUT(mk_imp(c,c))));;

(* ----- miscellany *)

let int_neg_as_minusnum1 = prove(`
  !i:int. i < &0 ==> ?m. i = -- &(m + 1)
  `,
  REPEAT STRIP_TAC THEN
  DISJ_CASES_TAC(SPEC `i:int` INT_IMAGE) THENL [
    ASM_MESON_TAC[
      INT_ARITH `~(&n < &0:int)`
    ];
    choosevar `n:num` `i:int = -- &n` [] THEN
    note `~(n = 0)` [INT_ARITH `~(-- &0 < &0:int)`] THEN
    choosevar `m:num` `n = SUC m` [num_CASES] THEN
    ASM_MESON_TAC[
      ARITH_RULE `SUC m = m + 1`
    ]
  ]
);;

let real_lt_ldiv = prove(`
  !x y z. &0:real < x /\ y < z * x ==> y / x < z
  `,
  REPEAT STRIP_TAC THEN
  note `&0 < inv x` [REAL_LT_INV] THEN
  note `y * inv x < (z * x) * inv x` [REAL_LT_RMUL] THEN
  real_linear `y * inv x < (z * x) * inv x ==> y / x < z * (x * inv x)` THEN
  real_linear `&0:real < x ==> ~(x = &0)` THEN
  note `x * inv x = &1` [REAL_MUL_RINV] THEN
  ASM_MESON_TAC[REAL_ARITH `z * &1:real = z`]
);;

let real_lt_rdiv_one_extra = prove(`
  !a b c:real.
  &0 < a /\ &1 <= b /\ c * (a * b) < a ==> c < &1
  `,
  REPEAT STRIP_TAC THEN
  note `&0 < inv a` [REAL_LT_INV] THEN
  note `(c * (a * b)) * inv a < a * inv a` [REAL_LT_RMUL] THEN
  real_linear `(c * (a * b)) * inv a < a * inv a ==> c * b * (a * inv a) < a * inv a` THEN
  real_linear `&0 < a ==> ~(a = &0:real)` THEN
  note `a * inv a = &1` [REAL_MUL_RINV] THEN
  real_linear `c * b * &1 = c * b:real` THEN
  note `c * b < &1:real` [] THEN
  ASM_CASES_TAC `&1 <= c:real` THENL [
    real_linear `&0 <= &1:real` THEN
    note `&1 * &1 <= c*b:real` [REAL_LE_MUL2] THEN
    real_linear `&1 * &1 <= c*b:real ==> ~(c * b < &1)`
  ;
    real_linear `~(&1 <= c:real) ==> c < &1`
  ] THEN
  ASM_MESON_TAC[]
);;

let real_lt_extra2 = prove(`
  !a b c d:real.
  a < b * c * d /\ &0 < a /\ &0 < d /\ d < &1 ==> a < b * c
  `,
  REPEAT STRIP_TAC THEN
  real_linear `&0 < d ==> ~(d = &0:real)` THEN
  note `d * inv d = &1` [REAL_MUL_RINV] THEN
  note `&0 < inv d` [REAL_LT_INV] THEN
  note `a * inv d < (b * c * d) * inv d` [REAL_LT_RMUL] THEN
  real_linear `a * inv d < (b * c * d) * inv d ==> a / d < b * c * (d * inv d)` THEN
  note `a / d < b * c * &1` [] THEN
  real_linear `b * c * &1:real = b * c` THEN
  note `a / d < b * c` [] THEN
  note `&0 < a / d` [REAL_LT_DIV] THEN
  note `d * (a / d) < &1 * (a / d)` [REAL_LT_RMUL] THEN
  real_cancel `&0 < d ==> d * (a / d) = a` THEN
  real_linear `&1 * (a / d) = a / d` THEN
  note `a < a / d` [] THEN
  ASM_MESON_TAC[REAL_LT_TRANS]
);;

(* ----- how to manipulate edge inequalities *)

let generic_1_Ppos = prove(`
  !D a b c d e f M00 M01 M10 M11 M P Q x y:real.
  &0 < D ==>
  &0 <= M ==>
  &0 < P ==>
  &0 < Q ==>
  M*a*D = Q*(d*M00+e*M10) ==>
  M*b*D = Q*(d*M01+e*M11) ==>
  M*c+P = Q*f ==>
  a*x+b*y <= c ==>
  d*(M00*x+M01*y)/D+e*(M10*x+M11*y)/D <= f
  `,
  REPEAT STRIP_TAC THEN
  real_cancel `&0:real < D ==> (M*a*D)/D = M*a` THEN
  real_cancel `&0:real < D ==> (M*b*D)/D = M*b` THEN
  note `M*a:real = (Q*(d*M00+e*M10))/D` [] THEN
  note `M*b:real = (Q*(d*M01+e*M11))/D` [] THEN
  note `M*(a*x+b*y) <= M*c:real` [REAL_LE_LMUL] THEN
  real_linear `&0 < P ==> M*c <= M*c+P` THEN
  note `M*(a*x+b*y) <= M*c+P:real` [REAL_LE_TRANS] THEN
  real_linear `M*(a*x+b*y) = (M*a)*x+(M*b)*y:real` THEN
  note `((Q*(d*M00+e*M10))/D)*x+((Q*(d*M01+e*M11))/D)*y <= Q*f:real` [] THEN
  real_cancel `&0:real < D ==> ((Q*(d*M00+e*M10))/D)*x+((Q*(d*M01+e*M11))/D)*y = Q*(d*(M00*x+M01*y)/D+e*(M10*x+M11*y)/D)` THEN
  note `Q*(d*(M00*x+M01*y)/D+e*(M10*x+M11*y)/D) <= Q*f:real` [] THEN
  ASM_MESON_TAC[REAL_LE_LMUL_EQ]
);;

let generic_1_P0 = prove(`
  !D a b c d e f M00 M01 M10 M11 M Q x y:real.
  &0 < D ==>
  &0 <= M ==>
  &0 < Q ==>
  M*a*D = Q*(d*M00+e*M10) ==>
  M*b*D = Q*(d*M01+e*M11) ==>
  M*c = Q*f ==>
  a*x+b*y <= c ==>
  d*(M00*x+M01*y)/D+e*(M10*x+M11*y)/D <= f
  `,
  REPEAT STRIP_TAC THEN
  real_cancel `&0:real < D ==> (M*a*D)/D = M*a` THEN
  real_cancel `&0:real < D ==> (M*b*D)/D = M*b` THEN
  note `M*a:real = (Q*(d*M00+e*M10))/D` [] THEN
  note `M*b:real = (Q*(d*M01+e*M11))/D` [] THEN
  note `M*(a*x+b*y) <= M*c:real` [REAL_LE_LMUL] THEN
  real_linear `M*(a*x+b*y) = (M*a)*x+(M*b)*y:real` THEN
  note `((Q*(d*M00+e*M10))/D)*x+((Q*(d*M01+e*M11))/D)*y <= Q*f:real` [] THEN
  real_cancel `&0:real < D ==> ((Q*(d*M00+e*M10))/D)*x+((Q*(d*M01+e*M11))/D)*y = Q*(d*(M00*x+M01*y)/D+e*(M10*x+M11*y)/D)` THEN
  note `Q*(d*(M00*x+M01*y)/D+e*(M10*x+M11*y)/D) <= Q*f:real` [] THEN
  ASM_MESON_TAC[REAL_LE_LMUL_EQ]
);;

let generic_2 = prove(`
  !D a b c d e f g h i M00 M01 M10 M11 M N P Q x y:real.
  &0 < D ==>
  &0 <= M ==>
  &0 <= N ==>
  &0 <= P ==>
  &0 < Q ==>
  (M*a+N*d)*D = Q*(g*M00+h*M10) ==>
  (M*b+N*e)*D = Q*(g*M01+h*M11) ==>
  M*c+N*f+P = Q*i ==>
  a*x+b*y <= c ==>
  d*x+e*y <= f ==>
  g*(M00*x+M01*y)/D+h*(M10*x+M11*y)/D <= i
  `,
  REPEAT STRIP_TAC THEN
  real_cancel `&0:real < D ==> ((M*a+N*d)*D)/D = M*a+N*d` THEN
  real_cancel `&0:real < D ==> ((M*b+N*e)*D)/D = M*b+N*e` THEN
  note `M*a+N*d:real = (Q*(g*M00+h*M10))/D` [] THEN
  note `M*b+N*e:real = (Q*(g*M01+h*M11))/D` [] THEN
  note `M*(a*x+b*y) <= M*c:real` [REAL_LE_LMUL] THEN
  note `N*(d*x+e*y) <= N*f:real` [REAL_LE_LMUL] THEN
  note `M*(a*x+b*y)+N*(d*x+e*y) <= M*c+N*f:real` [REAL_LE_ADD2] THEN
  real_linear `&0 <= P ==> M*c+N*f <= M*c+N*f+P` THEN
  note `M*(a*x+b*y)+N*(d*x+e*y) <= M*c+N*f+P:real` [REAL_LE_TRANS] THEN
  real_linear `M*(a*x+b*y)+N*(d*x+e*y) = (M*a+N*d)*x+(M*b+N*e)*y:real` THEN
  note `(M*a+N*d)*x+(M*b+N*e)*y <= M*c+N*f+P:real` [] THEN
  note `((Q*(g*M00+h*M10))/D)*x+((Q*(g*M01+h*M11))/D)*y <= Q*i:real` [] THEN
  real_cancel `&0:real < D ==> ((Q*(g*M00+h*M10))/D)*x+((Q*(g*M01+h*M11))/D)*y = Q*(g*(M00*x+M01*y)/D+h*(M10*x+M11*y)/D)` THEN
  note `Q*(g*(M00*x+M01*y)/D+h*(M10*x+M11*y)/D) <= Q*i:real` [] THEN
  ASM_MESON_TAC[REAL_LE_LMUL_EQ]
);;

'''

def hol_ZZ(z):
  z = ZZ(z)
  if z < 0:
    z = abs(z)
    return '-- &%d' % z
  return '&%d' % z

def hol_QQ(r):
  r = QQ(r)
  if r in ZZ:
    return hol_ZZ(r)
  if r < 0:
    r = abs(r)
    return '-- &%s / &%s' % (r.numerator(),r.denominator())
  return '&%s / &%s' % (r.numerator(),r.denominator())

def hol_float(f):
  # could do hol_QQ(QQ(f))
  # but sage conversion to QQ is buggy: QQ(RealIntervalField(8)(31415).upper()) < 31415
  # also, want to avoid large outputs for large exponents

  s,m,e = f.sign_mantissa_exponent()
  assert s in (1,-1)
  if m != 0:
    while m%2 == 0:
      m = ZZ(m/2)
      e += 1

  signprefix = '-- ' if s == -1 else ''
  if e > 0:
    return '%s&%s * &2 pow %d' % (signprefix,m,e)
  if e < 0:
    return '%s&%s / &2 pow %d' % (signprefix,m,-e)
  return '%s&%s' % (signprefix,m)
  
if approx:
  divsteps_qs_setup = f'note `divsteps_s = {hol_QQ(s)}` [divsteps_s] THEN\n  note `&0 < divsteps_s` [divsteps_s]'

  specialize_qs = 'specialize[`divsteps_s`]'
  specialize_qsxy = 'specialize[`divsteps_s`;`x:real`;`y:real`]'

  def hol_qsbasics():
    return fr'''(* ----- s *)

let divsteps_s_definition = new_definition `
  divsteps_s = {hol_QQ(s)}
`;;

let divsteps_s = prove(`
  divsteps_s = {hol_QQ(s)} /\
  &0 < divsteps_s
`,
  REWRITE_TAC[divsteps_s_definition] THEN
  REAL_ARITH_TAC
);;

(* one piece copied from Library/analysis.ml *)
let REAL_LE_RDIV = prove(
  `!x y z. &0 < x /\ (y * x) <= z ==> y <= (z / x)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC EQ_IMP THEN
  SUBGOAL_THEN `z = (z / x) * x` MP_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
    CONV_TAC(RAND_CONV SYM_CONV) THEN
    MATCH_MP_TAC REAL_LT_IMP_NE THEN POP_ASSUM ACCEPT_TAC;
    DISCH_THEN(fun t -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [t])
    THEN MATCH_MP_TAC REAL_LE_RMUL_EQ THEN POP_ASSUM ACCEPT_TAC]);;

'''

  def plusprojreduce(v):
    v = list(v)

    G = lcm(vj.denominator() for vj in v)
    v = [vj*G for vj in v]

    G = gcd(v)
    v = [vj/G for vj in v]

    return v

else:
  hol_qpoly_divsteps = hol_qpoly.replace('q','divsteps_q')
  hol_spoly_divsteps = hol_spoly.replace('s','divsteps_s').replace('q','divsteps_q')

  divsteps_qs_setup = fr'''note `{hol_qpoly_divsteps} = &0` [divsteps_q] THEN
  note `&0 < divsteps_q` [divsteps_q] THEN
  note `{hol_spoly_divsteps} = &0` [divsteps_s] THEN
  note `&0 < divsteps_s` [divsteps_s]'''

  specialize_qs = 'specialize[`divsteps_q`;`divsteps_s`]'
  specialize_qsxy = 'specialize[`divsteps_q`;`divsteps_s`;`x:real`;`y:real`]'
  
  def hol_qsbasics():
    return r'''(* ----- q and s *)

needs "Library/transc.ml";;

let root_pos = prove(`
  !x n.
  &0 < x ==> &0 < root(SUC n) x
  `,
  REPEAT STRIP_TAC THEN
  note `&0:real <= x` [REAL_LT_IMP_LE] THEN
  note `&0 <= root(SUC n) x` [ROOT_POS_POSITIVE] THEN
  ASM_CASES_TAC `root(SUC n) x = &0` THENL [
    note `(root(SUC n) x) pow (SUC n) = x` [ROOT_POW_POS] THEN
    num_linear `~(SUC n = 0)` THEN
    note `&0 pow (SUC n) = &0:real` [REAL_POW_ZERO] THEN
    real_linear `&0:real < x ==> ~(x = &0)` THEN
    ASM_MESON_TAC[]
  ;
    ASM_REAL_ARITH_TAC
  ]
  );;

let divsteps_q_definition = new_definition `
  divsteps_q = @q:real.
  %s = &0 /\ &0 < q
`;;

let divsteps_s_definition = new_definition `
  divsteps_s = @s:real.
  %s = &0 /\ &0 < s
`;;

let divsteps_q = prove(`
  %s = &0 /\ &0 < divsteps_q
  `,
  REWRITE_TAC[divsteps_q_definition] THEN
  SELECT_ELIM_TAC THEN
  EXISTS_TAC `sqrt(&%d)` THEN
  real_linear `&0:real < &%d` THEN
  ASM_MESON_TAC[
    SQRT_WORKS;
    SQRT_POS_LT;
    REAL_LT_IMP_LE;
    REAL_ARITH `q pow 2 = &%d ==> %s = &0:real`
  ]
  );;

let divsteps_s = prove(`
  %s = &0 /\ &0 < divsteps_s
  `,
  REWRITE_TAC[divsteps_s_definition] THEN
  SELECT_ELIM_TAC THEN
  EXISTS_TAC `root 54 ((divsteps_q * &3 + &1591853137) / &2 pow 55)` THEN
  num_linear `54 = SUC 53` THEN
  note `&0 < divsteps_q` [divsteps_q] THEN
  real_linear `&0:real < &3` THEN
  real_linear `&0:real < &1591853137` THEN
  real_linear `&0:real < &2 pow 55` THEN
  note `&0 < ((divsteps_q * &3 + &1591853137) / &2 pow 55)` [REAL_LT_MUL;REAL_LT_ADD;REAL_LT_DIV] THEN
  ASM_MESON_TAC[
    REAL_LT_IMP_LE;
    ROOT_POW_POS;
    root_pos;
    REAL_ARITH `s pow 54 = ((divsteps_q * &3 + &1591853137) / &2 pow 55) ==> %s = &0:real`
  ]
  );;
  
  ''' % (
      hol_qpoly,
      hol_spoly.replace('q','divsteps_q'),
      hol_qpoly.replace('q','divsteps_q'),
      Delta,Delta,Delta,hol_qpoly,
      hol_spoly.replace('s','divsteps_s').replace('q','divsteps_q'),
      hol_spoly.replace('q','divsteps_q'),
    )
  
  def plusprojreduce(v):
    v = list(v)
  
    sparse = []
    for j,rj in enumerate(v):
      for k,rjk in enumerate(L(rj)):
        if rjk != 0:
          sparse += [(j,k,K(rjk))]
  
    G = lcm(K(rjk).denominator() for j,k,rjk in sparse)
    sparse = [(j,k,2*G*rjk) for j,k,rjk in sparse]
  
    G = gcd(ZZ(d) for j,k,rjk in sparse for d in rjk)
    sparse = [(j,k,rjk/G) for j,k,rjk in sparse]
  
    if all(Delta.divides(ZZ(rjk[0])) for j,k,rjk in sparse):
      sparse = [(j,k,rjk/q) for j,k,rjk in sparse]
  
    norms = [ZZ(abs(rjk.norm())) for j,k,rjk in sparse]
    norms.sort()
    minnorm = norms[0]
    if all(minnorm.divides(N) for N in norms):
      alpha = next(rjk for j,k,rjk in sparse if abs(rjk.norm()) == minnorm)
      if Lsign(alpha) < 0: alpha = -alpha
      if all(alpha.divides(rjk) for j,k,rjk in sparse):
        sparse = [(j,k,rjk/alpha) for j,k,rjk in sparse]
  
    # XXX: can do more general gcd
    # but pari often overflows
  
    if any(d not in ZZ for j,k,rjk in sparse for d in rjk):
      sparse = [(j,k,2*rjk) for j,k,rjk in sparse]
  
    rotation = min(k for j,k,rjk in sparse)
    sparse = [(j,k-rotation,rjk) for j,k,rjk in sparse]
  
    result = [L(0)]*len(v)
    for j,k,rjk in sparse:
      result[j] += rjk*s^k
  
    for i in range(len(v)):
      for j in range(i):
        assert result[j]*v[i] == result[i]*v[j]
  
    return result

# input: convex hull H
# input: position i specifying edge H[i],H[i+1] with indices taken modulo len(H)
# output: xcoeff,ycoeff,target defining edge constraint
def edgeconstraint(H,i):
  A0,A1 = H[i%len(H)]
  B0,B1 = H[(i+1)%len(H)]
  xcoeff = B1-A1
  ycoeff = A0-B0
  target = B1*A0-B0*A1
  return plusprojreduce([xcoeff,ycoeff,target])

# sequence of xcoeff,ycoeff,target defining convex hull H
@memoized
def constraints(H):
  assert len(H) >= 3
  return [edgeconstraint(H,i) for i in range(len(H))]

def lemma1(spow,matrix,hypotheses,conclusion):
  (a,b,c), = hypotheses
  d,e,f = conclusion
  d,e = vector((d,e))*matrix/s^spow

  asign = Lsign(a)
  if asign > 0:
    M,Q = d,a
  elif asign < 0:
    M,Q = -d,-a
  elif Lsign(b) > 0:
    M,Q = e,b
  else:
    M,Q = -e,-b

  M,Q = plusprojreduce([M,Q])
  P = Q*f-M*c

  check = False
  if check:
    assert M*a == Q*d
    assert M*b == Q*e
    assert M*c+P == Q*f
    assert Lsign(M) >= 0
    assert Lsign(P) >= 0
    assert Lsign(Q) > 0

  return spow,matrix,tuple(hypotheses),tuple(conclusion),(M,P,Q)

def lemma2(spow,matrix,hypotheses,conclusion):
  (a,b,c),(d,e,f) = hypotheses
  g,h,i = conclusion
  g,h = vector((g,h))*matrix/s^spow

  M = g*e-h*d
  N = h*a-g*b
  Q = a*e-b*d
  if Lsign(Q) < 0:
    M,N,Q = -M,-N,-Q
  P = Q*i-M*c-N*f

  M,N,P,Q = plusprojreduce([M,N,P,Q])

  check = False
  if check:
    assert M*a+N*d == Q*g
    assert M*b+N*e == Q*h
    assert M*c+N*f+P == Q*i
    assert Lsign(M) >= 0
    assert Lsign(N) >= 0
    assert Lsign(P) >= 0
    assert Lsign(Q) > 0

  return spow,matrix,tuple(hypotheses),tuple(conclusion),(M,N,P,Q)

def lemmas_inclusion(spow,matrix,oldH,newH):
  result = []

  constraintsoldH = constraints(oldH)
  constraintsnewH = constraints(newH)

  for conclusion in constraintsnewH:
    def rating(x,y):
      x,y = matrix*vector((x,y))/s^spow
      return conclusion[0]*x+conclusion[1]*y
    ratings = [rating(x,y) for x,y in oldH]
    ratingsmaxpos = Lmaxpos(ratings)
    assert len(ratingsmaxpos) <= 2
    if len(ratingsmaxpos) == 2:
      if ratingsmaxpos[1] == ratingsmaxpos[0]+1:
        hypotheses = [constraintsoldH[ratingsmaxpos[0]]]
      else:
        assert ratingsmaxpos[0] == ratingsmaxpos[1]+1-len(oldH)
        hypotheses = [constraintsoldH[ratingsmaxpos[1]]]
    else:
      assert len(ratingsmaxpos) == 1
      hypotheses = [constraintsoldH[ratingsmaxpos[0]-1],constraintsoldH[ratingsmaxpos[0]]]

    lemma = lemma1 if len(hypotheses) == 1 else lemma2
    result += [lemma(spow,matrix,hypotheses,conclusion)]

  return result

def hol_linearcol(matrix,col,x,y):
  return '((%s) * %s + (%s) * %s)' % (x,hol_QQ(matrix[0][col]),y,hol_QQ(matrix[1][col]))

if approx:
  def hol_L(x):
    return hol_QQ(x)

  def hol_L_divsteps(x):
    return hol_QQ(x)

  def hol_QQxy(v):
    v = QQxy(v)
    result = '&0'
    for j,vj in enumerate(v):
      if vj == 0: continue
      data = '%s' % hol_QQ(abs(vj))
      if j == 1: data += ' * s'
      if j > 1: data += ' * s pow %d' % j
      if vj < 0: result += ' - %s' % data
      if vj > 0: result += ' + %s' % data
    if result.startswith('&0 + '): result = result[5:]
    if result.startswith('&0 - '): result = '-- '+result[5:]
    return result

  def hol_QQxy_divsteps(v):
    return hol_QQxy(v).replace('s','divsteps_s')

  def prove_equality1(spow,matrix,hypotheses,conclusion,aux):
    assert len(hypotheses) == 1
    (a,b,c), = hypotheses
    d,e,f = conclusion
    M,P,Q = aux
    xya,xyb,xyc,xyd,xye,xyf,xyM,xyP,xyQ = map(QQxy_from_L,(a,b,c,d,e,f,M,P,Q))
    hol_a,hol_b,hol_c,hol_d,hol_e,hol_f,hol_M,hol_P,hol_Q = map(hol_QQxy,(xya,xyb,xyc,xyd,xye,xyf,xyM,xyP,xyQ))

    assert M*a*s^spow == Q*(matrix[0][0]*d+matrix[1][0]*e)
    assert M*b*s^spow == Q*(matrix[0][1]*d+matrix[1][1]*e)
    if P == 0:
      assert M*c == Q*f
    else:
      assert M*c+P == Q*f

    if P == 0:
      result = fr'''REAL_ARITH `
  ({hol_M})*({hol_a})*({hol_L(s)}) pow {spow} = ({hol_Q})*({hol_linearcol(matrix,0,hol_d,hol_e)}) /\
  ({hol_M})*({hol_b})*({hol_L(s)}) pow {spow} = ({hol_Q})*({hol_linearcol(matrix,1,hol_d,hol_e)}) /\
  ({hol_M})*({hol_c}) = ({hol_Q})*({hol_f})
`'''
    else:
      result = fr'''REAL_ARITH `
  ({hol_M})*({hol_a})*({hol_L(s)}) pow {spow} = ({hol_Q})*({hol_linearcol(matrix,0,hol_d,hol_e)}) /\
  ({hol_M})*({hol_b})*({hol_L(s)}) pow {spow} = ({hol_Q})*({hol_linearcol(matrix,1,hol_d,hol_e)}) /\
  ({hol_M})*({hol_c})+({hol_P}) = ({hol_Q})*({hol_f})
`'''

    return result

  def prove_equality2(spow,matrix,hypotheses,conclusion,aux):
    assert len(hypotheses) == 2
    (a,b,c),(d,e,f) = hypotheses
    g,h,i = conclusion
    M,N,P,Q = aux
    xya,xyb,xyc,xyd,xye,xyf,xyg,xyh,xyi,xyM,xyN,xyP,xyQ = map(QQxy_from_L,(a,b,c,d,e,f,g,h,i,M,N,P,Q))
    hol_a,hol_b,hol_c,hol_d,hol_e,hol_f,hol_g,hol_h,hol_i,hol_M,hol_N,hol_P,hol_Q = map(hol_QQxy,(xya,xyb,xyc,xyd,xye,xyf,xyg,xyh,xyi,xyM,xyN,xyP,xyQ))

    result = fr'''REAL_ARITH `
  (({hol_M})*({hol_a})+({hol_N})*({hol_d}))*({hol_L(s)}) pow {spow} = ({hol_Q})*({hol_linearcol(matrix,0,hol_g,hol_h)}) /\
  (({hol_M})*({hol_b})+({hol_N})*({hol_e}))*({hol_L(s)}) pow {spow} = ({hol_Q})*({hol_linearcol(matrix,1,hol_g,hol_h)}) /\
  ({hol_M})*({hol_c})+({hol_N})*({hol_f})+({hol_P}) = ({hol_Q})*({hol_i})
`'''

    return result

else:
  @memoized
  def QQx_from_K(u):
    result = QQx(0)
    for k,uk in enumerate(u):
      result += uk*x^k
    return result
  
  @memoized
  def QQxy_from_L(v):
    v = L(v)
    result = QQxy(0)
    for j,vj in enumerate(v):
      result += QQx_from_K(vj)*y^j
    return result
  
  def hol_QQxy(v):
    v = QQxy(v)
    result = '&0'
    for j,vj in enumerate(v):
      for k,vjk in enumerate(vj):
        if vjk == 0: continue
        data = '%s' % hol_QQ(abs(vjk))
        if k == 1: data += ' * q'
        if k > 1: data += ' * q pow %d' % k
        if j == 1: data += ' * s'
        if j > 1: data += ' * s pow %d' % j
        if vjk < 0: result += ' - %s' % data
        if vjk > 0: result += ' + %s' % data
    if result.startswith('&0 + '): result = result[5:]
    if result.startswith('&0 - '): result = '-- '+result[5:]
    return result
  
  def hol_QQxy_divsteps(v):
    return hol_QQxy(v).replace('s','divsteps_s').replace('q','divsteps_q')
  
  def hol_L(v):
    return hol_QQxy(QQxy_from_L(v))
  
  def hol_L_divsteps(v):
    return hol_QQxy_divsteps(QQxy_from_L(v))
  
  def quotients(R):
    yquo,R = R//spoly,R%spoly
    xquo,R = R//qpoly,R%qpoly
    assert R == 0
    return xquo,yquo
  
  def prove_equality1(spow,matrix,hypotheses,conclusion,aux):
    assert len(hypotheses) == 1
  
    (a,b,c), = hypotheses
    d,e,f = conclusion
    M,P,Q = aux
    xya,xyb,xyc,xyd,xye,xyf,xyM,xyP,xyQ = map(QQxy_from_L,(a,b,c,d,e,f,M,P,Q))
    hol_a,hol_b,hol_c,hol_d,hol_e,hol_f,hol_M,hol_P,hol_Q = map(hol_QQxy,(xya,xyb,xyc,xyd,xye,xyf,xyM,xyP,xyQ))
  
    result = 'prove(`\n'
    if P == 0:
      result += '  !q s a b c d e f M Q:real.\n'
    else:
      result += '  !q s a b c d e f M P Q:real.\n'
    result += '  %s = &0 ==>\n' % hol_qpoly
    result += '  %s = &0 ==>\n' % hol_spoly
    if P == 0:
      for vstr,hol_v in ('a',hol_a),('b',hol_b),('c',hol_c),('d',hol_d),('e',hol_e),('f',hol_f),('M',hol_M),('Q',hol_Q):
        result += '  %s = %s ==>\n' % (vstr,hol_v)
    else:
      for vstr,hol_v in ('a',hol_a),('b',hol_b),('c',hol_c),('d',hol_d),('e',hol_e),('f',hol_f),('M',hol_M),('P',hol_P),('Q',hol_Q):
        result += '  %s = %s ==>\n' % (vstr,hol_v)
    result += '  M*a*s pow %d = Q*%s /\\\n' % (spow,hol_linearcol(matrix,0,'d','e'))
    result += '  M*b*s pow %d = Q*%s /\\\n' % (spow,hol_linearcol(matrix,1,'d','e'))
    if P == 0:
      result += '  M*c = Q*f\n'
    else:
      result += '  M*c+P = Q*f\n'
    result += '  `,\n'
    result += '  REPEAT GEN_TAC THEN\n'
    result += '  STRIP_TAC THEN STRIP_TAC THEN\n'
    xquo,yquo = quotients(xyM*xya*y^spow-xyQ*(xyd*matrix[0][0]+xye*matrix[1][0]))
    data = hol_M,hol_a,spow,hol_Q,hol_linearcol(matrix,0,hol_d,hol_e),hol_QQxy(yquo),hol_spoly,hol_QQxy(xquo),hol_qpoly
    result += '  real_linear `(%s)*(%s)*s pow %d = (%s)*(%s) + (%s)*(%s) + (%s)*(%s):real` THEN\n' % data
    xquo,yquo = quotients(xyM*xyb*y^spow-xyQ*(xyd*matrix[0][1]+xye*matrix[1][1]))
    data = hol_M,hol_b,spow,hol_Q,hol_linearcol(matrix,1,hol_d,hol_e),hol_QQxy(yquo),hol_spoly,hol_QQxy(xquo),hol_qpoly
    result += '  real_linear `(%s)*(%s)*s pow %d = (%s)*(%s) + (%s)*(%s) + (%s)*(%s):real` THEN\n' % data
    if P == 0:
      xquo,yquo = quotients(xyM*xyc-xyQ*xyf)
      data = hol_M,hol_c,hol_Q,hol_f,hol_QQxy(yquo),hol_spoly,hol_QQxy(xquo),hol_qpoly
      result += '  real_linear `(%s)*(%s) = (%s)*(%s) + (%s)*(%s) + (%s)*(%s):real` THEN\n' % data
    else:
      xquo,yquo = quotients(xyM*xyc+xyP-xyQ*xyf)
      data = hol_M,hol_c,hol_P,hol_Q,hol_f,hol_QQxy(yquo),hol_spoly,hol_QQxy(xquo),hol_qpoly
      result += '  real_linear `(%s)*(%s)+(%s) = (%s)*(%s) + (%s)*(%s) + (%s)*(%s):real` THEN\n' % data
    result += '  ASM_SIMP_TAC[\n'
    result += '    REAL_ARITH `c + d * (&0:real) + e * &0 = c`\n'
    result += '  ]\n'
    result += ')'
    return result
  
  def prove_equality2(spow,matrix,hypotheses,conclusion,aux):
    assert len(hypotheses) == 2
    (a,b,c),(d,e,f) = hypotheses
    g,h,i = conclusion
    M,N,P,Q = aux
    xya,xyb,xyc,xyd,xye,xyf,xyg,xyh,xyi,xyM,xyN,xyP,xyQ = map(QQxy_from_L,(a,b,c,d,e,f,g,h,i,M,N,P,Q))
    hol_a,hol_b,hol_c,hol_d,hol_e,hol_f,hol_g,hol_h,hol_i,hol_M,hol_N,hol_P,hol_Q = map(hol_QQxy,(xya,xyb,xyc,xyd,xye,xyf,xyg,xyh,xyi,xyM,xyN,xyP,xyQ))
  
    result = 'prove(`\n'
    result += '  !q s a b c d e f g h i M N P Q:real.\n'
    result += '  %s = &0 ==>\n' % hol_qpoly
    result += '  %s = &0 ==>\n' % hol_spoly
    for vstr,hol_v in ('a',hol_a),('b',hol_b),('c',hol_c),('d',hol_d),('e',hol_e),('f',hol_f),('g',hol_g),('h',hol_h),('i',hol_i),('M',hol_M),('N',hol_N),('P',hol_P),('Q',hol_Q):
      result += '  %s = %s ==>\n' % (vstr,hol_v)
    result += '  (M*a+N*d)*s pow %d = Q*%s /\\\n' % (spow,hol_linearcol(matrix,0,'g','h'))
    result += '  (M*b+N*e)*s pow %d = Q*%s /\\\n' % (spow,hol_linearcol(matrix,1,'g','h'))
    result += '  M*c+N*f+P = Q*i\n'
    result += '  `,\n'
    result += '  REPEAT GEN_TAC THEN\n'
    result += '  STRIP_TAC THEN STRIP_TAC THEN\n'
    xquo,yquo = quotients((xyM*xya+xyN*xyd)*y^spow-xyQ*(xyg*matrix[0][0]+xyh*matrix[1][0]))
    data = hol_M,hol_a,hol_N,hol_d,spow,hol_Q,hol_linearcol(matrix,0,hol_g,hol_h),hol_QQxy(yquo),hol_spoly,hol_QQxy(xquo),hol_qpoly
    result += '  real_linear `((%s)*(%s)+(%s)*(%s))*s pow %d = (%s)*(%s) + (%s)*(%s) + (%s)*(%s)` THEN\n' % data
    xquo,yquo = quotients((xyM*xyb+xyN*xye)*y^spow-xyQ*(xyg*matrix[0][1]+xyh*matrix[1][1]))
    data = hol_M,hol_b,hol_N,hol_e,spow,hol_Q,hol_linearcol(matrix,1,hol_g,hol_h),hol_QQxy(yquo),hol_spoly,hol_QQxy(xquo),hol_qpoly
    result += '  real_linear `((%s)*(%s)+(%s)*(%s))*s pow %d = (%s)*(%s) + (%s)*(%s) + (%s)*(%s)` THEN\n' % data
    xquo,yquo = quotients(xyM*xyc+xyN*xyf+xyP-xyQ*xyi)
    data = hol_M,hol_c,hol_N,hol_f,hol_P,hol_Q,hol_i,hol_QQxy(yquo),hol_spoly,hol_QQxy(xquo),hol_qpoly
    result += '  real_linear `(%s)*(%s)+(%s)*(%s)+(%s) = (%s)*(%s) + (%s)*(%s) + (%s)*(%s)` THEN\n' % data
    result += '  ASM_SIMP_TAC[\n'
    result += '    REAL_ARITH `c + d * (&0:real) + e * &0 = c`\n'
    result += '  ]\n'
    result += ')'
    return result
  
def prove_equality(lemma):
  spow,matrix,hypotheses,conclusion,aux = lemma
  if len(hypotheses) == 1:
    return prove_equality1(*lemma)
  return prove_equality2(*lemma)

class proofdag():
  def __init__(self,proof,*dependencies):
    self._proof = tuple(proof)
    self._dependencies = tuple(dependencies)

  def linearize(self):
    def proof(t,handled):
      if t in handled: return ()
      handled.add(t)
      result = ()
      for u in t._dependencies:
        result += proof(u,handled)
      result += t._proof
      return result

    return proof(self,set())

proveinterval_lemmas = []

def hol_proveinterval_lemmas():
  result = ''
  for name,conclusion,proof in proveinterval_lemmas:
    proof = ' THEN\n  '.join(proof.linearize())
    result += f'''let {name} = prove(`
  !q s:real.
  {hol_qpoly} = &0 ==>
  &0 < q ==>
  {hol_spoly} = &0 ==>
  &0 < s ==>
  {conclusion}
  `,
  REPEAT STRIP_TAC THEN
  {proof} THEN
  ASM_MESON_TAC[]);;

'''
  return result

@memoized
def proveinterval_field(bits):
  class proveinterval_class():
    def __init__(self,*z,gt0=None,ge0=None):
      K = RI(bits)
      if len(z) == 1:
        z, = z
        z = QQ(z)
        I = K(z)
        name = '%s:real' % hol_QQ(z)
        lowerdep = ()
        provelower = ['real_linear `%s`']
        upperdep = ()
        proveupper = ['real_linear `%s`']
      else:
        name,I,provelower,lowerdep,proveupper,upperdep = z

      lower = hol_float(I.lower())
      upper = hol_float(I.upper())
      statelower = '%s <= %s' % (lower,name)
      stateupper = '%s <= %s' % (name,upper)
      provelower = provelower[:-1] + [provelower[-1] % statelower]
      proveupper = proveupper[:-1] + [proveupper[-1] % stateupper]

      self.name = name
      self.field = K
      self.interval = I
      self.lower = lower
      self.upper = upper
      self.statelower = statelower
      self.stateupper = stateupper
      self.lowertree = proofdag(provelower,*lowerdep)
      self.uppertree = proofdag(proveupper,*upperdep)

      if 0 < I:
        self.lowergt0 = proofdag(['real_linear `&0:real < %s`' % lower])
        self.gt0 = proofdag(['note `&0:real < %s` [REAL_LTE_TRANS]' % name],self.lowertree,self.lowergt0)
        self.lowerge0 = proofdag(['note `&0:real <= %s` [REAL_LT_IMP_LE]' % lower],self.lowergt0)
        self.ge0 = proofdag(['note `&0:real <= %s` [REAL_LT_IMP_LE]' % name],self.gt0)
      elif 0 <= I:
        self.lowerge0 = proofdag(['real_linear `&0:real <= %s`' % lower])
        self.ge0 = proofdag(['note `&0:real <= %s` [REAL_LE_TRANS]' % name],self.lowertree,self.lowerge0)

      # overriding proofs via lower bounds
      if gt0 is not None: self.gt0 = gt0
      if ge0 is not None: self.ge0 = ge0

    def is_definitely_gt0(self):
      return 0 < self.interval

    def is_definitely_ge0(self):
      return 0 <= self.interval

    def rename(self,name,*renamedeps):
      I = self.interval
      provelower = ['note `%s` []']
      lowerdep = (self.lowertree,)+renamedeps
      proveupper = ['note `%s` []']
      upperdep = (self.uppertree,)+renamedeps
      return proveinterval_class(name,I,provelower,lowerdep,proveupper,upperdep)

    def __add__(self,other):
      if isinstance(other,proveinterval_class) and other.field() == self.field():
        I = self.interval+other.interval
        name = '(%s)+(%s)' % (self.name,other.name)
        provelower = ['real_linear `%s /\\ %s ==> %%s`' % (self.statelower,other.statelower)]
        lowerdep = self.lowertree,other.lowertree
        proveupper = ['real_linear `%s /\\ %s ==> %%s`' % (self.stateupper,other.stateupper)]
        upperdep = self.uppertree,other.uppertree
        return proveinterval_class(name,I,provelower,lowerdep,proveupper,upperdep)

      z = QQ(other)
      I = self.interval+z
      name = '(%s)+(%s)' % (self.name,hol_QQ(z))
      provelower = ['real_linear `%s ==> %%s`' % self.statelower]
      lowerdep = self.lowertree,
      proveupper = ['real_linear `%s ==> %%s`' % self.stateupper]
      upperdep = self.uppertree,
      return proveinterval_class(name,I,provelower,lowerdep,proveupper,upperdep)

    # XXX: not actually used...
    def __sub__(self,other):
      if isinstance(other,proveinterval_class) and other.field() == self.field():
        I = self.interval-other.interval
        name = '(%s)-(%s)' % (self.name,other.name)
        provelower = ['real_linear `%s /\\ %s ==> %%s`' % (self.statelower,other.stateupper)]
        lowerdep = self.lowertree,other.uppertree
        proveupper = ['real_linear `%s /\\ %s ==> %%s`' % (self.stateupper,other.statelower)]
        upperdep = self.uppertree,other.lowertree
        return proveinterval_class(name,I,provelower,lowerdep,proveupper,upperdep)

      z = QQ(other)
      I = self.interval-z
      name = '(%s)-(%s)' % (self.name,hol_QQ(z))
      provelower = ['real_linear `%s ==> %%s`' % self.statelower]
      lowerdep = self.lowertree,
      proveupper = ['real_linear `%s ==> %%s`' % self.stateupper]
      upperdep = self.uppertree,
      return proveinterval_class(name,I,provelower,lowerdep,proveupper,upperdep)

    def __mul__(self,other):
      if isinstance(other,proveinterval_class) and other.field() == self.field():
        # XXX: handle the negative cases too
        I = self.interval*other.interval
        name = '(%s)*(%s)' % (self.name,other.name)
        provelower = [
          'note `(%s)*(%s) <= (%s)*(%s)` [REAL_LE_MUL2]' % (self.lower,other.lower,self.name,other.name),
          'real_linear `%s <= (%s)*(%s)`' % (hol_float(I.lower()),self.lower,other.lower),
          'note `%s` [REAL_LE_TRANS]'
        ]
        lowerdep = self.lowertree,other.lowertree,self.lowerge0,other.lowerge0
        proveupper = [
          'note `(%s)*(%s) <= (%s)*(%s)` [REAL_LE_MUL2]' % (self.name,other.name,self.upper,other.upper),
          'real_linear `(%s)*(%s) <= %s`' % (self.upper,other.upper,hol_float(I.upper())),
          'note `%s` [REAL_LE_TRANS]'
        ]
        upperdep = self.uppertree,other.uppertree,self.ge0,other.ge0

        gt0 = None
        if self.is_definitely_gt0() and other.is_definitely_gt0():
          gt0 = proofdag(['note `&0:real < %s` [REAL_LT_MUL]' % name],self.gt0,other.gt0)
        ge0 = None
        if self.is_definitely_ge0() and other.is_definitely_ge0():
          ge0 = proofdag(['note `&0:real <= %s` [REAL_LE_MUL]' % name],self.ge0,other.ge0)
        
        return proveinterval_class(name,I,provelower,lowerdep,proveupper,upperdep,gt0=gt0,ge0=ge0)

      z = QQ(other)
      if z >= 0:
        I = self.interval*z
        name = '(%s)*(%s)' % (self.name,hol_QQ(z))
        provelower = ['real_linear `%s ==> %%s`' % self.statelower]
        lowerdep = self.lowertree,
        proveupper = ['real_linear `%s ==> %%s`' % self.stateupper]
        upperdep = self.uppertree,
        return proveinterval_class(name,I,provelower,lowerdep,proveupper,upperdep)

      I = self.interval*z
      name = '(%s)*(%s)' % (self.name,hol_QQ(z))
      provelower = ['real_linear `%s ==> %%s`' % self.stateupper]
      lowerdep = self.uppertree,
      proveupper = ['real_linear `%s ==> %%s`' % self.statelower]
      upperdep = self.lowertree,
      return proveinterval_class(name,I,provelower,lowerdep,proveupper,upperdep)

    def square(self):
      I = self.interval^2
      name = '(%s) pow 2' % self.name
      provelower = [
        'note `(%s) pow 2 <= (%s) pow 2` [REAL_LE_MUL2;REAL_POW_2]' % (self.lower,self.name),
        'real_linear `%s <= (%s) pow 2`' % (hol_float(I.lower()),self.lower),
        'note `%s` [REAL_LE_TRANS]'
      ]
      lowerdep = self.lowertree,self.lowerge0
      proveupper = [
        'note `(%s) pow 2 <= (%s) pow 2` [REAL_LE_MUL2;REAL_POW_2]' % (self.name,self.upper),
        'real_linear `(%s) pow 2 <= %s`' % (self.upper,hol_float(I.upper())),
        'note `%s` [REAL_LE_TRANS]'
      ]
      upperdep = self.uppertree,self.ge0

      gt0 = None
      if self.is_definitely_gt0():
        gt0 = proofdag(['note `&0:real < %s` [REAL_LT_MUL;REAL_POW_2]' % name],self.gt0)
      ge0 = None
      if self.is_definitely_ge0():
        ge0 = proofdag(['note `&0:real <= %s` [REAL_LE_MUL;REAL_POW_2]' % name],self.ge0)

      return proveinterval_class(name,I,provelower,lowerdep,proveupper,upperdep,gt0=gt0,ge0=ge0)

    def __truediv__(self,other):
      z = QQ(other)
      if z <= 0:
        raise ValueError('z = %s is negative; division by negative numbers currently not supported' % z)
      I = self.interval/z
      name = '(%s)/(%s)' % (self.name,hol_QQ(z))
      provelower = ['real_linear `%s ==> %%s`' % self.statelower]
      lowerdep = self.lowertree,
      proveupper = ['real_linear `%s ==> %%s`' % self.stateupper]
      upperdep = self.uppertree,
      return proveinterval_class(name,I,provelower,lowerdep,proveupper,upperdep)

    def root(self,n,*nonnegdeps):
      n = ZZ(n)
      if n < 1:
        raise ValueError('n = %d is below 1; currently only positive integers are supported')

      powname = self.name
      if not (powname.startswith('(') and powname.endswith(') pow %d'%n)):
        raise ValueError('name "%s" does not have the format (...) pow %d' % (name,n))
      rootname = powname[1:-len(') pow %d'%n)]

      # XXX: also allow negative numbers
      I = self.interval^(1/n)
      rootlower = hol_float(I.lower())
      provelower = [
        'real_linear `(%s) pow %d <= %s`' % (rootlower,n,hol_float(self.interval.lower())),
        'note `(%s) pow %d <= %s` [REAL_LE_TRANS]' % (rootlower,n,powname),
        'note `%%s` [REAL_POW_LE2_REV;ARITH_RULE `~(%d = 0)`]' % n
      ]
      lowerdep = (self.lowertree,)+nonnegdeps
      rootupper = hol_float(I.upper())
      proveupper = [
        'real_linear `%s <= (%s) pow %d`' % (hol_float(self.interval.upper()),rootupper,n),
        'note `%s <= (%s) pow %d` [REAL_LE_TRANS]' % (powname,rootupper,n),
        'real_linear `&0 <= %s`' % rootupper,
        'note `%%s` [REAL_POW_LE2_REV;ARITH_RULE `~(%d = 0)`]' % n
      ]
      upperdep = self.uppertree,
      return proveinterval_class(rootname,I,provelower,lowerdep,proveupper,upperdep)

    def proof_gt0(self):
      return self.gt0.linearize()

    def makelemma(self,L):
      name = self.name
      lower = hol_float(self.interval.lower())
      upper = hol_float(self.interval.upper())

      lemmaname = L+'_lower'
      conclusion = f'({lower}):real <= {name}'
      proveinterval_lemmas.append((lemmaname,conclusion,self.lowertree))
      self.lowertree = proofdag([f'note `{conclusion}` [{lemmaname}]'])

      lemmaname = L+'_upper'
      conclusion = f'{name} <= ({upper}):real'
      proveinterval_lemmas.append((lemmaname,conclusion,self.uppertree))
      self.uppertree = proofdag([f'note `{conclusion}` [{lemmaname}]'])

      if 0 < self.interval:
        lemmaname = L+'_lowergt0'
        conclusion = f'&0:real < {lower}'
        proveinterval_lemmas.append((lemmaname,conclusion,self.lowergt0))
        self.lowergt0 = proofdag([f'note `{conclusion}` [{lemmaname}]'])

        # XXX: merge across bits
        lemmaname = L+'_gt0'
        conclusion = f'&0:real < {name}'
        proveinterval_lemmas.append((lemmaname,conclusion,self.gt0))
        self.gt0 = proofdag([f'note `{conclusion}` [{lemmaname}]'])

      if 0 <= self.interval:
        lemmaname = L+'_lowerge0'
        conclusion = f'&0:real <= {lower}'
        proveinterval_lemmas.append((lemmaname,conclusion,self.lowerge0))
        self.lowerge0 = proofdag([f'note `{conclusion}` [{lemmaname}]'])

        # XXX: merge across bits
        lemmaname = L+'_ge0'
        conclusion = f'&0:real <= {name}'
        proveinterval_lemmas.append((lemmaname,conclusion,self.ge0))
        self.ge0 = proofdag([f'note `{conclusion}` [{lemmaname}]'])

      return self

  return proveinterval_class

def monomials(I_x,I_y,xyexp):
  xyexp = set((ZZ(j),ZZ(k)) for j,k in xyexp)

  xexp = set(j for j,k in xyexp)
  yexp = set(k for j,k in xyexp)
  assert all(j >= 0 for j in xexp)
  assert all(k >= 0 for k in xexp)

  for E in xexp,yexp:
    for i in list(E):
      while i > 0:
        i = i-1 if i%2 == 1 else ZZ(i/2)
        E.add(i)
  for j in xexp: xyexp.add((j,0))
  for k in yexp: xyexp.add((0,k))

  result = {}
  for j,k in sorted(xyexp):
    if (j,k) == (0,0):
      result[j,k] = parent(I_x)(1)
    elif (j,k) == (1,0):
      result[j,k] = I_x
    elif (j,k) == (0,1):
      result[j,k] = I_y
    elif k == 0 and j%2 == 1:
      result[j,k] = result[j-1,k]*I_x
    elif k == 0:
      result[j,k] = result[ZZ(j/2),k].square()
    elif j == 0 and k%2 == 1:
      result[j,k] = result[j,k-1]*I_y
    elif j == 0:
      result[j,k] = result[j,ZZ(k/2)].square()
    else:
      result[j,k] = result[j,0]*result[0,k]

  return result

if approx:
  def prove_positive_poly(P):
    return f'prove(`!s:real. s = {hol_L(s)} ==> &0:real < {hol_QQxy(P)}`,REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC)'
  
  def prove_positive(beta):
    return f'REAL_ARITH `!s:real. &0:real < {hol_QQ(beta)}`'

  def hol_positive_lemmas():
    return ''

else:
  q_provepow2 = proofdag(['real_linear `%s = &0:real ==> q pow 2 = &%d`' % (hol_qpoly,Delta)])
  q_provenonneg = proofdag(['note `&0:real <= q` [REAL_LT_IMP_LE]'])
  
  @memoized
  def q_proveinterval(bits):
    K = proveinterval_field(bits)
    I_q2 = K(Delta).rename('(q:real) pow 2',q_provepow2)
    I_q = I_q2.root(2,q_provenonneg)
    return I_q.makelemma(f'q_{bits}')
  
  s_provepow54 = proofdag(['real_linear `%s = &0:real ==> s pow 2 pow 3 pow 3 pow 3 = (q * &3 + &1591853137) / &36028797018963968`' % hol_spoly])
  s_provenonneg = proofdag(['note `&0:real <= s` [REAL_LT_IMP_LE]'])
  s_provepow2nonneg = proofdag(['note `&0:real <= s pow 2` [REAL_POW_LT;REAL_LT_IMP_LE]'])
  s_provepow6nonneg = proofdag(['note `&0:real <= s pow 2 pow 3` [REAL_POW_LT;REAL_LT_IMP_LE]'])
  s_provepow18nonneg = proofdag(['note `&0:real <= s pow 2 pow 3 pow 3` [REAL_POW_LT;REAL_LT_IMP_LE]'])
  
  @memoized
  def s_proveinterval(bits):
    I_q = q_proveinterval(bits)
    I_3q = I_q*3
    I_3qplusc = I_3q+1591853137
    I_s54 = (I_3qplusc/2^55).rename('((((s:real) pow 2) pow 3) pow 3) pow 3',s_provepow54)
    I_s18 = I_s54.root(3,s_provepow18nonneg)
    I_s6 = I_s18.root(3,s_provepow6nonneg)
    I_s2 = I_s6.root(3,s_provepow2nonneg)
    I_s = I_s2.root(2,s_provenonneg)
    return I_s.makelemma(f's_{bits}')
  
  def prove_positive_steps(sparse):
    bits = 8
    while True:
      I_q = q_proveinterval(bits)
      I_s = s_proveinterval(bits)
      I_sqpow = monomials(I_s,I_q,[(j,k) for j,k,betajk in sparse])
      result = None
      for j,k,betajk in sparse:
        term = I_sqpow[j,k]*betajk
        result = term if result is None else result+term
      if result.is_definitely_gt0():
        return result.name,result.proof_gt0()
  
      bits += bits//4
  
  positive_lemmas = ''
  positive_lemmanames = {}
  
  def hol_positive_lemmas():
    return positive_lemmas
  
  def prove_positive_poly_inner(P):
    global positive_lemmas
  
    if P in positive_lemmanames:
      return positive_lemmanames[P]
  
    assert Lsign(P(s,q)) >= 0
  
    result = 'prove(`\n'
    result += '  !q s:real.\n'
    result += '  %s = &0 ==>\n' % hol_qpoly
    result += '  &0 < q ==>\n'
    result += '  %s = &0 ==>\n' % hol_spoly
    result += '  &0 < s ==>\n'
    result += '  &0:real < %s\n' % hol_QQxy(P)
    result += '  `,\n'
  
    sparse = QQxysparse(P)
  
    if all(0 < Pjk for j,k,Pjk in sparse):
      result += '  MESON_TAC[\n'
      for j,k,Pjk in sparse:
        result += '    REAL_ARITH `&0 < %s`;\n' % hol_QQ(Pjk)
      result += '    REAL_POW_LT;\n'
      result += '    REAL_LT_MUL;\n'
      result += '    REAL_LT_ADD;\n'
      result += '  ]\n'
    
    else:
      result += '  REPEAT STRIP_TAC THEN\n'
      name,proof = prove_positive_steps(sparse)
      result += '  %s THEN\n' % ' THEN\n  '.join(proof)
      result += '  ASM_MESON_TAC[REAL_ARITH `%s = %s`]\n' % (name,hol_QQxy(P))
  
    result += ')'
  
    name = 'positive_'
    for j,k,Pjk in sparse:
      name += f'{j}_{k}_{"M" if Pjk<0 else ""}{abs(Pjk.numerator())}_{Pjk.denominator()}'
  
    positive_lemmas += f'let {name} =\n{result};;\n\n'
    positive_lemmanames[P] = name
    return name
  
  def prove_positive_poly(P):
    P = QQxy(P)
    return prove_positive_poly_inner(P)
  
  def prove_positive(beta):
    return prove_positive_poly(QQxy_from_L(beta))

def prove_edge1(spow,matrix,hypotheses,conclusion,aux,eqproof):
  assert len(hypotheses) == 1
  (a,b,c), = hypotheses
  d,e,f = conclusion
  M,P,Q = aux
  hol_a,hol_b,hol_c,hol_d,hol_e,hol_f,hol_M,hol_P,hol_Q = map(hol_L,(a,b,c,d,e,f,M,P,Q))

  result = 'let mpos = %s in\n' % prove_positive(M)
  if P != 0:
    result += 'let ppos = %s in\n' % prove_positive(P)

  result += 'let qpos = %s in\n' % prove_positive(Q)
  result += 'let mqrel = %s in\n' % eqproof
  result += 'prove(`\n'
  if approx:
    result += '  !s x y:real.\n'
    result += f'  s = {hol_L(s)} ==>\n'
  else:
    result += '  !q s x y:real.\n'
    result += '  %s = &0 ==>\n' % hol_qpoly
    result += '  &0 < q ==>\n'
    result += '  %s = &0 ==>\n' % hol_spoly
    result += '  &0 < s ==>\n'
  result += '  (%s) * x + (%s) * y <= %s ==>\n' % (hol_a,hol_b,hol_c)
  result += '  (%s) * ((%s) * x + (%s) * y) / s pow %d + (%s) * ((%s) * x + (%s) * y) / s pow %d <= %s\n' % (hol_d,hol_QQ(matrix[0][0]),hol_QQ(matrix[0][1]),spow,hol_e,hol_QQ(matrix[1][0]),hol_QQ(matrix[1][1]),spow,hol_f)
  result += '  `,\n'
  result += '  REPEAT STRIP_TAC THEN\n'
  result += '  note `&0:real < %s` [mpos] THEN\n' % hol_M
  if P != 0:
    result += '  note `&0:real < %s` [ppos] THEN\n' % hol_P
  result += '  note `&0:real < %s` [qpos] THEN\n' % hol_Q
  result += '  note `&0:real < s pow %d` [REAL_POW_LT] THEN\n' % spow
  if P == 0:
    result += '  note `(%s)*(%s)*s pow %d = (%s)*((%s) * %s + (%s) * %s) /\\ (%s)*(%s)*s pow %d = (%s)*((%s) * %s + (%s) * %s) /\\ (%s)*(%s) = (%s)*(%s)` [mqrel] THEN\n' % (
      hol_M, hol_a, spow, hol_Q, hol_d, hol_QQ(matrix[0][0]), hol_e, hol_QQ(matrix[1][0]),
      hol_M, hol_b, spow, hol_Q, hol_d, hol_QQ(matrix[0][1]), hol_e, hol_QQ(matrix[1][1]),
      hol_M, hol_c, hol_Q, hol_f,
    )
    result += '  ASM_MESON_TAC[generic_1_P0;REAL_LT_IMP_LE]\n'
  else:
    result += '  note `(%s)*(%s)*s pow %d = (%s)*((%s) * %s + (%s) * %s) /\\ (%s)*(%s)*s pow %d = (%s)*((%s) * %s + (%s) * %s) /\\ (%s)*(%s)+(%s) = (%s)*(%s)` [mqrel] THEN\n' % (
      hol_M, hol_a, spow, hol_Q, hol_d, hol_QQ(matrix[0][0]), hol_e, hol_QQ(matrix[1][0]),
      hol_M, hol_b, spow, hol_Q, hol_d, hol_QQ(matrix[0][1]), hol_e, hol_QQ(matrix[1][1]),
      hol_M, hol_c, hol_P, hol_Q, hol_f,
    )
    result += '  ASM_MESON_TAC[generic_1_Ppos;REAL_LT_IMP_LE]\n'
  result += ')'

  return result

def prove_edge2(spow,matrix,hypotheses,conclusion,aux,eqproof):
  assert len(hypotheses) == 2
  (a,b,c),(d,e,f) = hypotheses
  g,h,i = conclusion
  M,N,P,Q = aux
  hol_a,hol_b,hol_c,hol_d,hol_e,hol_f,hol_g,hol_h,hol_i,hol_M,hol_N,hol_P,hol_Q = map(hol_L,(a,b,c,d,e,f,g,h,i,M,N,P,Q))

  result = 'let mpos = %s in\n' % prove_positive(M)
  result += 'let npos = %s in\n' % prove_positive(N)
  if P != 0:
    result += 'let ppos = %s in\n' % prove_positive(P)
  result += 'let qpos = %s in\n' % prove_positive(Q)
  result += 'let mqrel = %s in\n' % eqproof

  result += 'prove(`\n'
  if approx:
    result += '  !s x y:real.\n'
    result += f'  s = {hol_L(s)} ==>\n'
  else:
    result += '  !q s x y:real.\n'
    result += '  %s = &0 ==>\n' % hol_qpoly
    result += '  &0 < q ==>\n'
    result += '  %s = &0 ==>\n' % hol_spoly
  result += '  &0 < s ==>\n'
  result += '  (%s) * x + (%s) * y <= %s ==>\n' % (hol_a,hol_b,hol_c)
  result += '  (%s) * x + (%s) * y <= %s ==>\n' % (hol_d,hol_e,hol_f)
  result += '  (%s) * ((%s) * x + (%s) * y) / s pow %d + (%s) * ((%s) * x + (%s) * y) / s pow %d <= %s\n' % (hol_g,hol_QQ(matrix[0][0]),hol_QQ(matrix[0][1]),spow,hol_h,hol_QQ(matrix[1][0]),hol_QQ(matrix[1][1]),spow,hol_i)
  result += '  `,\n'
  result += '  REPEAT STRIP_TAC THEN\n'
  result += '  note `&0:real < %s` [mpos] THEN\n' % hol_M
  result += '  note `&0:real < %s` [npos] THEN\n' % hol_N
  if P == 0:
    result += '  real_linear `&0:real <= &0` THEN\n'
  else:
    result += '  note `&0:real < %s` [ppos] THEN\n' % hol_P
  result += '  note `&0:real < %s` [qpos] THEN\n' % hol_Q
  result += '  note `&0:real < s pow %d` [REAL_POW_LT] THEN\n' % spow
  result += '  note `((%s)*(%s)+(%s)*(%s))*s pow %d = (%s)*((%s) * %s + (%s) * %s) /\\ ((%s)*(%s)+(%s)*(%s))*s pow %d = (%s)*((%s) * %s + (%s) * %s) /\\ (%s)*(%s)+(%s)*(%s)+(%s) = (%s)*(%s)` [mqrel] THEN\n' % (
    hol_M, hol_a, hol_N, hol_d, spow, hol_Q, hol_g, hol_QQ(matrix[0][0]), hol_h, hol_QQ(matrix[1][0]),
    hol_M, hol_b, hol_N, hol_e, spow, hol_Q, hol_g, hol_QQ(matrix[0][1]), hol_h, hol_QQ(matrix[1][1]),
    hol_M, hol_c, hol_N, hol_f, hol_P, hol_Q, hol_i,
  )
  result += '  ASM_MESON_TAC[generic_2;REAL_LT_IMP_LE]\n'
  result += ')'

  return result

def prove_edge(lemma):
  eqproof = prove_equality(lemma)
  spow,matrix,hypotheses,conclusion,aux = lemma
  if len(hypotheses) == 1:
    return prove_edge1(*lemma,eqproof)
  return prove_edge2(*lemma,eqproof)

@memoized
def hol_hull_base(H):
  C = constraints(H)
  return ' /\\\n  '.join(
    '(%s)*(X)+(%s)*(Y) <= %s' % (hol_L(a),hol_L(b),hol_L(c))
    for a,b,c in constraints(H)
  )

def hol_hull(H,x,y):
  return hol_hull_base(H).replace('X',x).replace('Y',y)

def hol_definehull(Hname,H):
  result = ''
  result += 'let divsteps_%s = new_definition `\n' % Hname
  result += '  divsteps_%s (x:real) (y:real) <=>\n' % Hname
  result += '  %s\n' % hol_hull(H,'x','y').replace('s','divsteps_s').replace('q','divsteps_q')
  result += '`;;\n'
  return result

@memoized
def prove_inclusion_inner(spow,M,oldHname,oldH,newHname,newH):
  lemmas = lemmas_inclusion(spow,M,oldH,newH)

  result = ''
  for j,lemmaj in enumerate(lemmas):
    result += 'let L%d =\n' % j
    result += prove_edge(lemmaj)
    result += ' in\n'

  result += fr'''prove(`
  !x:real y:real.
  divsteps_{oldHname} x y ==>
  divsteps_{newHname} ((({hol_QQ(M[0][0])}) * x + ({hol_QQ(M[0][1])}) * y) / divsteps_s pow {spow}) ((({hol_QQ(M[1][0])}) * x + ({hol_QQ(M[1][1])}) * y) / divsteps_s pow {spow})
  `,
  {divsteps_qs_setup} THEN
  REWRITE_TAC[divsteps_%s] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[divsteps_%s] THEN
  %s THEN
  ASM_SIMP_TAC[]
  )''' % (
    oldHname,
    newHname,
    ' THEN\n  '.join(f'{specialize_qsxy}L{j}' for j in range(len(newH)))
  )

  return result

def prove_inclusion(spow,M,oldHname,oldH,newHname,newH):
  return prove_inclusion_inner(spow,matrix(M,immutable=True),oldHname,oldH,newHname,newH)

def indent(proof):
  return proof.replace('\n','\n  ')

def prove_contains0(Hname,H):
  result = 'prove(`\n'
  result += '  divsteps_%s (&0) (&0)\n' % Hname
  result += '  `,\n'
  if not approx:
    result += '  note `%s = &0` [divsteps_q] THEN\n' % hol_qpoly.replace('q','divsteps_q')
    result += '  note `&0 < divsteps_q` [divsteps_q] THEN\n'
    result += '  note `%s = &0` [divsteps_s] THEN\n' % hol_spoly.replace('s','divsteps_s').replace('q','divsteps_q')
    result += '  note `&0 < divsteps_s` [divsteps_s] THEN\n'
  result += '  REWRITE_TAC[divsteps_%s] THEN\n' % Hname
  result += '  REWRITE_TAC[REAL_ARITH `c * &0 = &0:real`] THEN\n'
  result += '  REWRITE_TAC[REAL_ARITH `&0 + &0 = &0:real`] THEN\n'
  result += '  REPEAT STRIP_TAC THENL [\n'
  for a,b,c in constraints(H):
    result += f'    {specialize_qs}(%s) THEN ASM_MESON_TAC[REAL_LT_IMP_LE];\n' % indent(prove_positive(c))
  result += '  ])'
  return result

def prove_notcontains(Hname,H,ox,oy):
  for a,b,c in constraints(H):
    d = a*ox+b*oy-c
    if Lsign(d) > 0:
      xya,xyox,xyb,xyoy,xyc,xyd = map(QQxy_from_L,(a,ox,b,oy,c,d))
      hol_a,hol_ox,hol_b,hol_oy,hol_c,hol_d = map(hol_QQxy_divsteps,(xya,xyox,xyb,xyoy,xyc,xyd))

      if approx:
        result = 'prove(`\n'
        result += '  ~(divsteps_%s (%s) (%s))\n' % (Hname,hol_ox,hol_oy)
        result += '  `,\n'
        result += '  REWRITE_TAC[divsteps_%s] THEN\n' % Hname
        result += '  REAL_ARITH_TAC\n'
        result += '  )'
      else:
        result = 'prove(`\n'
        result += '  ~(divsteps_%s (%s) (%s))\n' % (Hname,hol_ox,hol_oy)
        result += '  `,\n'

        result += f'  {divsteps_qs_setup} THEN\n'
        result += f'  {specialize_qs}(%s) THEN\n' % indent(prove_positive(d))
      
        xquo,yquo = quotients(xya*xyox+xyb*xyoy-xyc-xyd)
        datashort = hol_a,hol_ox,hol_b,hol_oy,hol_c
        data = datashort+(hol_d,hol_QQxy_divsteps(yquo),hol_spoly_divsteps,hol_QQxy_divsteps(xquo),hol_qpoly_divsteps)
        result += '  real_linear `(%s)*(%s)+(%s)*(%s)-(%s) = (%s)+(%s)*(%s)+(%s)*(%s):real` THEN\n' % data
        data2 = data+(hol_qpoly_divsteps,hol_spoly_divsteps,hol_d)+datashort
        result += '  real_linear `(%s)*(%s)+(%s)*(%s)-(%s) = (%s)+(%s)*(%s)+(%s)*(%s):real /\\ %s = &0 /\\ %s = &0 /\\ &0:real < %s ==> ~((%s)*(%s)+(%s)*(%s) <= (%s):real)` THEN\n' % data2
        result += '  ASM_SIMP_TAC[divsteps_%s]\n' % Hname
        result += '  )'
      return result

  raise ValueError('hull contains (%s,%s)' % (ox,oy))

# ----- initial hull evolution

# did traveling from A to B and then to C turn left at B?
def leftturn(A,B,C):
  beta = (B[0]-A[0])*(A[1]-C[1])-(B[1]-A[1])*(A[0]-C[0])
  return Lsign(beta) < 0

# input: set (or tuple or list) S of points (x,y) in the plane
# output: convex hull of S
#   expressed as minimal list H of points
#   (in counterclockwise order, starting with lex min (x,y))
#   such that Hull(H) = Hull(S)
def compress(S):
  H = sorted(set(S),key=lambda ab:tuple(map(LtoRR,ab)))

  # monotone-chain algorithm, 1979 andrew
  if len(H) > 1:
    L = [] # lower hull
    for v in H:
      while len(L) >= 2 and not leftturn(L[-2],L[-1],v):
        L.pop()
      L += [v]
    U = [] # upper hull
    for v in reversed(H):
      while len(U) >= 2 and not leftturn(U[-2],U[-1],v):
        U.pop()
      U += [v]
    L.pop()
    U.pop()
    H = L+U

  return tuple(H)

def hullmap(M,H):
  H = [tuple(M*vector(v)) for v in H]
  return compress(H)

Hinit = {}
Hinitname = {}
Hinit[0,1/2] = (0,0),(1,0),(1,1)
deltarange = [1/2]
initialsteps = 0 # XXX
for pos in range(initialsteps):
  newdeltarange = [1+delta for delta in deltarange]
  newdeltarange += [1-delta for delta in deltarange]
  newdeltarange = sorted(set(newdeltarange))
  for delta in newdeltarange:
    Hinit[pos+1,delta] = []
  for delta in deltarange:
    Hinit[pos+1,1+delta] += hullmap(UP0,Hinit[pos,delta])
    if delta < 0:
      Hinit[pos+1,1+delta] += hullmap(UP1,Hinit[pos,delta])
    else:
      Hinit[pos+1,1-delta] += hullmap(DOWN,Hinit[pos,delta])
  for delta in newdeltarange:
    Hinit[pos+1,delta] = compress(Hinit[pos+1,delta])
  deltarange = newdeltarange

for pos in range(initialsteps+1):
  for delta in deltarange:
    if (pos,delta) not in Hinit: continue
    if delta > 0:
      Hinitname[pos,delta] = 'hinit_%d_%d'%(pos,2*delta)
    else:
      Hinitname[pos,delta] = 'hinit_%d_M%d'%(pos,-2*delta)

def hol_initialhulls():
  result = '(* ----- initial hulls *)\n\n'
  for pos in range(initialsteps+1):
    for delta in deltarange:
      if (pos,delta) not in Hinit: continue
      result += hol_definehull(Hinitname[pos,delta],Hinit[pos,delta])
      result += '\n'
  return result

# ----- stable hull

if approx:
  H0 = (
    (-44273/65536,6315/65536), # 0
    (-21891/32768,13/65536), # 1
    (-43467/65536,-733/32768), # 2
    (-20575/32768,-615/4096), # 3
    (-20339/32768,-5747/32768), # 4
    (-9993/16384,-13579/65536), # 5
    (-39819/65536,-13989/65536), # 6
    (-8431/16384,-937/2048), # 7
    (-33531/65536,-30471/65536), # 8
    (-3989/8192,-17093/32768), # 9
    (-13933/32768,-41799/65536), # 10
    (-26257/65536,-44329/65536), # 11
    (-24133/65536,-11863/16384), # 12
    (-2963/8192,-48057/65536), # 13
    (-721/2048,-48733/65536), # 14
    (-17877/65536,-53149/65536), # 15
    (-8859/32768,-26637/32768), # 16
    (-4105/16384,-54071/65536), # 17
    (-5845/32768,-14027/16384), # 18
    (-7945/65536,-56941/65536), # 19
    (-6547/65536,-28471/32768), # 20
    (-2371/32768,-56799/65536), # 21
    (-2191/32768,-56753/65536), # 22
    (9713/65536,-54777/65536), # 23
    (317/2048,-13677/16384), # 24
    (167/1024,-54473/65536), # 25
    (3691/16384,-25887/32768), # 26
    (3161/8192,-21299/32768), # 27
    (28695/65536,-39141/65536), # 28
    (1835/4096,-9611/16384), # 29
    (3767/8192,-37455/65536), # 30
    (30281/65536,-37247/65536), # 31
    (8963/16384,-28993/65536), # 32
    (18009/32768,-28735/65536), # 33
    (18595/32768,-26631/65536), # 34
    (5095/8192,-1185/4096), # 35
    (21477/32768,-6443/32768), # 36
    (43521/65536,-5309/32768), # 37
    (22069/32768,-7691/65536), # 38
    (22123/32768,-7107/65536), # 39
    (44273/65536,-6315/65536), # 40
    (21891/32768,-13/65536), # 41
    (43467/65536,733/32768), # 42
    (20575/32768,615/4096), # 43
    (20339/32768,5747/32768), # 44
    (9993/16384,13579/65536), # 45
    (39819/65536,13989/65536), # 46
    (8431/16384,937/2048), # 47
    (33531/65536,30471/65536), # 48
    (3989/8192,17093/32768), # 49
    (13933/32768,41799/65536), # 50
    (26257/65536,44329/65536), # 51
    (24133/65536,11863/16384), # 52
    (2963/8192,48057/65536), # 53
    (721/2048,48733/65536), # 54
    (17877/65536,53149/65536), # 55
    (8859/32768,26637/32768), # 56
    (4105/16384,54071/65536), # 57
    (5845/32768,14027/16384), # 58
    (7945/65536,56941/65536), # 59
    (6547/65536,28471/32768), # 60
    (2371/32768,56799/65536), # 61
    (2191/32768,56753/65536), # 62
    (-9713/65536,54777/65536), # 63
    (-317/2048,13677/16384), # 64
    (-167/1024,54473/65536), # 65
    (-3691/16384,25887/32768), # 66
    (-3161/8192,21299/32768), # 67
    (-28695/65536,39141/65536), # 68
    (-1835/4096,9611/16384), # 69
    (-3767/8192,37455/65536), # 70
    (-30281/65536,37247/65536), # 71
    (-8963/16384,28993/65536), # 72
    (-18009/32768,28735/65536), # 73
    (-18595/32768,26631/65536), # 74
    (-5095/8192,1185/4096), # 75
    (-21477/32768,6443/32768), # 76
    (-43521/65536,5309/32768), # 77
    (-22069/32768,7691/65536), # 78
    (-22123/32768,7107/65536), # 79
  )
  H1 = (
    (-65537/65536,-11711/65536), # 0
    (-16203/16384,-8093/32768), # 1
    (-59139/65536,-29595/65536), # 2
    (-58727/65536,-15177/32768), # 3
    (-55597/65536,-17223/32768), # 4
    (-3435/4096,-8811/16384), # 5
    (-27003/32768,-2261/4096), # 6
    (-53799/65536,-18175/32768), # 7
    (-45563/65536,-43037/65536), # 8
    (-45303/65536,-10809/16384), # 9
    (-10779/16384,-11163/16384), # 10
    (-37649/65536,-47061/65536), # 11
    (-8869/16384,-11921/16384), # 12
    (-16303/32768,-48359/65536), # 13
    (-32025/65536,-48477/65536), # 14
    (-7793/16384,-48507/65536), # 15
    (-23999/65536,-23985/32768), # 16
    (-11103/32768,-47623/65536), # 17
    (-11761/65536,-45085/65536), # 18
    (-9691/65536,-5571/8192), # 19
    (-1755/16384,-43795/65536), # 20
    (-6487/65536,-43627/65536), # 21
    (7189/32768,-36949/65536), # 22
    (1877/8192,-18369/32768), # 23
    (19973/65536,-8741/16384), # 24
    (30531/65536,-30531/65536), # 25
    (4273/8192,-899/2048), # 26
    (38769/65536,-26441/65536), # 27
    (9917/16384,-12985/32768), # 28
    (20377/32768,-25279/65536), # 29
    (48439/65536,-9793/32768), # 30
    (48663/65536,-4853/16384), # 31
    (25123/32768,-8995/32768), # 32
    (27535/32768,-1601/8192), # 33
    (29017/32768,-8705/65536), # 34
    (58801/65536,-7173/65536), # 35
    (29817/32768,-1299/16384), # 36
    (14945/16384,-4801/65536), # 37
    (65337/65536,5321/32768), # 38
    (65497/65536,5557/32768), # 39
    (65537/65536,11711/65536), # 40
    (16203/16384,8093/32768), # 41
    (59139/65536,29595/65536), # 42
    (58727/65536,15177/32768), # 43
    (55597/65536,17223/32768), # 44
    (3435/4096,8811/16384), # 45
    (27003/32768,2261/4096), # 46
    (53799/65536,18175/32768), # 47
    (45563/65536,43037/65536), # 48
    (45303/65536,10809/16384), # 49
    (10779/16384,11163/16384), # 50
    (37649/65536,47061/65536), # 51
    (8869/16384,11921/16384), # 52
    (16303/32768,48359/65536), # 53
    (32025/65536,48477/65536), # 54
    (7793/16384,48507/65536), # 55
    (23999/65536,23985/32768), # 56
    (11103/32768,47623/65536), # 57
    (11761/65536,45085/65536), # 58
    (9691/65536,5571/8192), # 59
    (1755/16384,43795/65536), # 60
    (6487/65536,43627/65536), # 61
    (-7189/32768,36949/65536), # 62
    (-1877/8192,18369/32768), # 63
    (-19973/65536,8741/16384), # 64
    (-30531/65536,30531/65536), # 65
    (-4273/8192,899/2048), # 66
    (-38769/65536,26441/65536), # 67
    (-9917/16384,12985/32768), # 68
    (-20377/32768,25279/65536), # 69
    (-48439/65536,9793/32768), # 70
    (-48663/65536,4853/16384), # 71
    (-25123/32768,8995/32768), # 72
    (-27535/32768,1601/8192), # 73
    (-29017/32768,8705/65536), # 74
    (-58801/65536,7173/65536), # 75
    (-29817/32768,1299/16384), # 76
    (-14945/16384,4801/65536), # 77
    (-65337/65536,-5321/32768), # 78
    (-65497/65536,-5557/32768), # 79
  )
else:
  H1 = ( # 1/2
   ( -1 , -237081/1329130 ), # 0
   ( -347440232139479/363581859795880922302810*q-1/2 , -11486026214601/66105792690160167691420*q-237081/2658260 ), # 1
   ( -239996/132913*s^2 , -297966/664565*s^2 ), # 2
   ( (-313500554932274/181790929897940461151405*q-119998/132913)*s^2 , (-1439514140379/3305289634508008384571*q-148983/664565)*s^2 ), # 3
   ( -156750277466137/181790929897940461151405*q-59999/132913 , -315096832907827/727163719591761844605620*q-597961/2658260 ), # 4
   ( (320792913/21776465920*q-170218401628806027/21776465920)*s^39 , (663072411/87105863680*q-351837965836167769/87105863680)*s^39 ), # 5
   ( (-18679743837609394176/181790929897940461151405*q-38654705664/664565)*s^39 , (-2227121567257591808/36358185979588092230281*q-17179869184/664565)*s^39 ), # 6
   ( -771751936/664565*s^24 , -478150656/664565*s^24 ), # 7
   ( (-197195608384077824/181790929897940461151405*q-385875968/664565)*s^24 , (-130837732632035328/181790929897940461151405*q-239075328/664565)*s^24 ), # 8
   ( -8215552/664565*s^9 , -5503232/664565*s^9 ), # 9
   ( (-426398219768320/36358185979588092230281*q-4107776/664565)*s^9 , (-1452958194442624/181790929897940461151405*q-2751616/664565)*s^9 ), # 10
   ( -12652544/664565*s^11 , -1086464/60415*s^11 ), # 11
   ( (-3271004213106688/181790929897940461151405*q-6326272/664565)*s^11 , (-3154160885029376/181790929897940461151405*q-543232/60415)*s^11 ), # 12
   ( (3152991/10633040*q-1673032871427589/10633040)*s^50 , (2606913/8506432*q-1383274212312027/8506432)*s^50 ), # 13
   ( (-298896352880667656192/181790929897940461151405*q-4294967296/3091)*s^50 , (-459790200791384457216/181790929897940461151405*q-670014898176/664565)*s^50 ), # 14
   ( -4294967296/664565*s^31 , -1073741824/132913*s^31 ), # 15
   ( (-993490117408587776/181790929897940461151405*q-2147483648/664565)*s^31 , (-1441093077824438272/181790929897940461151405*q-536870912/132913)*s^31 ), # 16
   ( -40763392/664565*s^16 , -12091392/132913*s^16 ), # 17
   ( (-10280385951629312/181790929897940461151405*q-20381696/664565)*s^16 , (-1444331613929472/16526448172540041922855*q-6045696/132913)*s^16 ), # 18
   ( -427484/664565*s , -s ), # 19
   ( (-110546971889434/181790929897940461151405*q-213742/664565)*s , (-347440232139479/363581859795880922302810*q-1/2)*s ), # 20
   ( -604048/664565*s^3 , -239996/132913*s^3 ), # 21
   ( (-155153999490584/181790929897940461151405*q-302024/664565)*s^3 , (-313500554932274/181790929897940461151405*q-119998/132913)*s^3 ), # 22
   ( (37413291/2722058240*q-19852154881281289/2722058240)*s^42 , (320792913/10888232960*q-170218401628806027/10888232960)*s^42 ), # 23
   ( (-11496800167676346368/181790929897940461151405*q-4294967296/60415)*s^42 , (-37359487675218788352/181790929897940461151405*q-77309411328/664565)*s^42 ), # 24
   ( -402653184/664565*s^27 , -1543503872/664565*s^27 ), # 25
   ( (-13647178924818432/36358185979588092230281*q-201326592/664565)*s^27 , (-394391216768155648/181790929897940461151405*q-771751936/664565)*s^27 ), # 26
   ( -2633728/664565*s^12 , -16431104/664565*s^12 ), # 27
   ( (-584140518754304/181790929897940461151405*q-1316864/664565)*s^12 , (-852796439536640/36358185979588092230281*q-8215552/664565)*s^12 ), # 28
   ( 9846784/664565*s^14 , -25305088/664565*s^14 ), # 29
   ( (560726180159488/36358185979588092230281*q+4923392/664565)*s^14 , (-6542008426213376/181790929897940461151405*q-12652544/664565)*s^14 ), # 30
   ( (-446949/1329130*q+237159055909671/1329130)*s^53 , (3152991/5316520*q-1673032871427589/5316520)*s^53 ), # 31
   ( (942471744523534860288/181790929897940461151405*q-90194313216/664565)*s^53 , (-597792705761335312384/181790929897940461151405*q-8589934592/3091)*s^53 ), # 32
   ( 8589934592/664565*s^34 , -8589934592/664565*s^34 ), # 33
   ( (556780391814397952/36358185979588092230281*q+4294967296/664565)*s^34 , (-1986980234817175552/181790929897940461151405*q-4294967296/664565)*s^34 ), # 34
   ( 119537664/664565*s^19 , -81526784/664565*s^19 ), # 35
   ( (32709433158008832/181790929897940461151405*q+59768832/664565)*s^19 , (-20560771903258624/181790929897940461151405*q-40763392/664565)*s^19 ), # 36
   ( 1375808/664565*s^4 , -854968/664565*s^4 ), # 37
   ( (363239548610656/181790929897940461151405*q+687904/664565)*s^4 , (-221093943778868/181790929897940461151405*q-427484/664565)*s^4 ), # 38
   ( 271616/60415*s^6 , -1208096/664565*s^6 ), # 39
   ( (788540221257344/181790929897940461151405*q+135808/60415)*s^6 , (-310307998981168/181790929897940461151405*q-604048/664565)*s^6 ), # 40
   ( (-2606913/34025728*q+1383274212312027/34025728)*s^45 , (37413291/1361029120*q-19852154881281289/1361029120)*s^45 ), # 41
   ( (114947550197846114304/181790929897940461151405*q+167503724544/664565)*s^45 , (-22993600335352692736/181790929897940461151405*q-8589934592/60415)*s^45 ), # 42
   ( (-2606913/17012864*q+1383274212312027/17012864)*s^47 , (12189363/340257280*q-6467891909860577/340257280)*s^47 ), # 43
   ( (229895100395692228608/181790929897940461151405*q+335007449088/664565)*s^47 , (-1568210283749441536/16526448172540041922855*q-147102629888/664565)*s^47 ), # 44
   ( 536870912/132913*s^28 , -402653184/664565*s^28 ), # 45
   ( (720546538912219136/181790929897940461151405*q+268435456/132913)*s^28 , (-13647178924818432/36358185979588092230281*q-201326592/664565)*s^28 ), # 46
   ( 6045696/132913*s^13 , -2633728/664565*s^13 ), # 47
   ( (722165806964736/16526448172540041922855*q+3022848/132913)*s^13 , (-584140518754304/181790929897940461151405*q-1316864/664565)*s^13 ), # 48
   ( 12091392/132913*s^15 , 9846784/664565*s^15 ), # 49
   ( (1444331613929472/16526448172540041922855*q+6045696/132913)*s^15 , (560726180159488/36358185979588092230281*q+4923392/664565)*s^15 ), # 50
   ( 1 , 237081/1329130 ), # 51
   ( 347440232139479/363581859795880922302810*q+1/2 , 11486026214601/66105792690160167691420*q+237081/2658260 ), # 52
   ( 239996/132913*s^2 , 297966/664565*s^2 ), # 53
   ( (313500554932274/181790929897940461151405*q+119998/132913)*s^2 , (1439514140379/3305289634508008384571*q+148983/664565)*s^2 ), # 54
   ( 156750277466137/181790929897940461151405*q+59999/132913 , 315096832907827/727163719591761844605620*q+597961/2658260 ), # 55
   ( (-320792913/21776465920*q+170218401628806027/21776465920)*s^39 , (-663072411/87105863680*q+351837965836167769/87105863680)*s^39 ), # 56
   ( (18679743837609394176/181790929897940461151405*q+38654705664/664565)*s^39 , (2227121567257591808/36358185979588092230281*q+17179869184/664565)*s^39 ), # 57
   ( 771751936/664565*s^24 , 478150656/664565*s^24 ), # 58
   ( (197195608384077824/181790929897940461151405*q+385875968/664565)*s^24 , (130837732632035328/181790929897940461151405*q+239075328/664565)*s^24 ), # 59
   ( 8215552/664565*s^9 , 5503232/664565*s^9 ), # 60
   ( (426398219768320/36358185979588092230281*q+4107776/664565)*s^9 , (1452958194442624/181790929897940461151405*q+2751616/664565)*s^9 ), # 61
   ( 12652544/664565*s^11 , 1086464/60415*s^11 ), # 62
   ( (3271004213106688/181790929897940461151405*q+6326272/664565)*s^11 , (3154160885029376/181790929897940461151405*q+543232/60415)*s^11 ), # 63
   ( (-3152991/10633040*q+1673032871427589/10633040)*s^50 , (-2606913/8506432*q+1383274212312027/8506432)*s^50 ), # 64
   ( (298896352880667656192/181790929897940461151405*q+4294967296/3091)*s^50 , (459790200791384457216/181790929897940461151405*q+670014898176/664565)*s^50 ), # 65
   ( 4294967296/664565*s^31 , 1073741824/132913*s^31 ), # 66
   ( (993490117408587776/181790929897940461151405*q+2147483648/664565)*s^31 , (1441093077824438272/181790929897940461151405*q+536870912/132913)*s^31 ), # 67
   ( 40763392/664565*s^16 , 12091392/132913*s^16 ), # 68
   ( (10280385951629312/181790929897940461151405*q+20381696/664565)*s^16 , (1444331613929472/16526448172540041922855*q+6045696/132913)*s^16 ), # 69
   ( 427484/664565*s , s ), # 70
   ( (110546971889434/181790929897940461151405*q+213742/664565)*s , (347440232139479/363581859795880922302810*q+1/2)*s ), # 71
   ( 604048/664565*s^3 , 239996/132913*s^3 ), # 72
   ( (155153999490584/181790929897940461151405*q+302024/664565)*s^3 , (313500554932274/181790929897940461151405*q+119998/132913)*s^3 ), # 73
   ( (-37413291/2722058240*q+19852154881281289/2722058240)*s^42 , (-320792913/10888232960*q+170218401628806027/10888232960)*s^42 ), # 74
   ( (11496800167676346368/181790929897940461151405*q+4294967296/60415)*s^42 , (37359487675218788352/181790929897940461151405*q+77309411328/664565)*s^42 ), # 75
   ( 402653184/664565*s^27 , 1543503872/664565*s^27 ), # 76
   ( (13647178924818432/36358185979588092230281*q+201326592/664565)*s^27 , (394391216768155648/181790929897940461151405*q+771751936/664565)*s^27 ), # 77
   ( 2633728/664565*s^12 , 16431104/664565*s^12 ), # 78
   ( (584140518754304/181790929897940461151405*q+1316864/664565)*s^12 , (852796439536640/36358185979588092230281*q+8215552/664565)*s^12 ), # 79
   ( -9846784/664565*s^14 , 25305088/664565*s^14 ), # 80
   ( (-560726180159488/36358185979588092230281*q-4923392/664565)*s^14 , (6542008426213376/181790929897940461151405*q+12652544/664565)*s^14 ), # 81
   ( (446949/1329130*q-237159055909671/1329130)*s^53 , (-3152991/5316520*q+1673032871427589/5316520)*s^53 ), # 82
   ( (-942471744523534860288/181790929897940461151405*q+90194313216/664565)*s^53 , (597792705761335312384/181790929897940461151405*q+8589934592/3091)*s^53 ), # 83
   ( -8589934592/664565*s^34 , 8589934592/664565*s^34 ), # 84
   ( (-556780391814397952/36358185979588092230281*q-4294967296/664565)*s^34 , (1986980234817175552/181790929897940461151405*q+4294967296/664565)*s^34 ), # 85
   ( -119537664/664565*s^19 , 81526784/664565*s^19 ), # 86
   ( (-32709433158008832/181790929897940461151405*q-59768832/664565)*s^19 , (20560771903258624/181790929897940461151405*q+40763392/664565)*s^19 ), # 87
   ( -1375808/664565*s^4 , 854968/664565*s^4 ), # 88
   ( (-363239548610656/181790929897940461151405*q-687904/664565)*s^4 , (221093943778868/181790929897940461151405*q+427484/664565)*s^4 ), # 89
   ( -271616/60415*s^6 , 1208096/664565*s^6 ), # 90
   ( (-788540221257344/181790929897940461151405*q-135808/60415)*s^6 , (310307998981168/181790929897940461151405*q+604048/664565)*s^6 ), # 91
   ( (2606913/34025728*q-1383274212312027/34025728)*s^45 , (-37413291/1361029120*q+19852154881281289/1361029120)*s^45 ), # 92
   ( (-114947550197846114304/181790929897940461151405*q-167503724544/664565)*s^45 , (22993600335352692736/181790929897940461151405*q+8589934592/60415)*s^45 ), # 93
   ( (2606913/17012864*q-1383274212312027/17012864)*s^47 , (-12189363/340257280*q+6467891909860577/340257280)*s^47 ), # 94
   ( (-229895100395692228608/181790929897940461151405*q-335007449088/664565)*s^47 , (1568210283749441536/16526448172540041922855*q+147102629888/664565)*s^47 ), # 95
   ( -536870912/132913*s^28 , 402653184/664565*s^28 ), # 96
   ( (-720546538912219136/181790929897940461151405*q-268435456/132913)*s^28 , (13647178924818432/36358185979588092230281*q+201326592/664565)*s^28 ), # 97
   ( -6045696/132913*s^13 , 2633728/664565*s^13 ), # 98
   ( (-722165806964736/16526448172540041922855*q-3022848/132913)*s^13 , (584140518754304/181790929897940461151405*q+1316864/664565)*s^13 ), # 99
   ( -12091392/132913*s^15 , -9846784/664565*s^15 ), # 100
   ( (-1444331613929472/16526448172540041922855*q-6045696/132913)*s^15 , (-560726180159488/36358185979588092230281*q-4923392/664565)*s^15 ), # 101
  )
  H0 = ( # -1/2
   ( (3/4*q-1591853137/4)*s^53 , (-571209/5316520*q+303093612844211/5316520)*s^53 ), # 0
   ( (-962629219677060530176/181790929897940461151405*q-1946147946496/664565)*s^53 , (-30847497784611405824/16526448172540041922855*q+235633082368/132913)*s^53 ), # 1
   ( -119998/132913*s , 2029/664565*s ), # 2
   ( (-156750277466137/181790929897940461151405*q-59999/132913)*s , (-1596277975553/363581859795880922302810*q+2029/1329130)*s ), # 3
   ( (320792913/21776465920*q-170218401628806027/21776465920)*s^40 , (4297317/8710586368*q-2280232515711143/8710586368)*s^40 ), # 4
   ( (-18679743837609394176/181790929897940461151405*q-38654705664/664565)*s^40 , (-326497439542411264/16526448172540041922855*q+4294967296/664565)*s^40 ), # 5
   ( -771751936/664565*s^25 , -16777216/60415*s^25 ), # 6
   ( (-197195608384077824/181790929897940461151405*q-385875968/664565)*s^25 , (-64479856879992832/181790929897940461151405*q-8388608/60415)*s^25 ), # 7
   ( -8215552/664565*s^10 , -2790912/664565*s^10 ), # 8
   ( (-426398219768320/36358185979588092230281*q-4107776/664565)*s^10 , (-773925290043648/181790929897940461151405*q-1395456/664565)*s^10 ), # 9
   ( -12652544/664565*s^12 , -11249664/664565*s^12 ), # 10
   ( (-3271004213106688/181790929897940461151405*q-6326272/664565)*s^12 , (-3037317556952064/181790929897940461151405*q-5624832/664565)*s^12 ), # 11
   ( (3152991/10633040*q-1673032871427589/10633040)*s^51 , (6728583/21266080*q-3570305318704957/21266080)*s^51 ), # 12
   ( (-298896352880667656192/181790929897940461151405*q-4294967296/3091)*s^51 , (-124136809740420251648/36358185979588092230281*q-416611827712/664565)*s^51 ), # 13
   ( -4294967296/664565*s^32 , -6442450944/664565*s^32 ), # 14
   ( (-993490117408587776/181790929897940461151405*q-2147483648/664565)*s^32 , (-1888696038240288768/181790929897940461151405*q-3221225472/664565)*s^32 ), # 15
   ( -40763392/664565*s^17 , -80150528/664565*s^17 ), # 16
   ( (-10280385951629312/181790929897940461151405*q-20381696/664565)*s^17 , (-21494909554819072/181790929897940461151405*q-40075264/664565)*s^17 ), # 17
   ( -427484/664565*s^2 , -901646/664565*s^2 ), # 18
   ( (-110546971889434/181790929897940461151405*q-213742/664565)*s^2 , (-47378652050009/36358185979588092230281*q-450823/664565)*s^2 ), # 19
   ( -604048/664565*s^4 , -1795912/664565*s^4 ), # 20
   ( (-155153999490584/181790929897940461151405*q-302024/664565)*s^4 , (-10973188613348/4227696044138150259335*q-897956/664565)*s^4 ), # 21
   ( (37413291/2722058240*q-19852154881281289/2722058240)*s^43 , (245966331/5444116480*q-130514091866243449/5444116480)*s^43 ), # 22
   ( (-11496800167676346368/181790929897940461151405*q-4294967296/60415)*s^43 , (-63222175182761230336/181790929897940461151405*q-21474836480/132913)*s^43 ), # 23
   ( (12189363/680514560*q-6467891909860577/680514560)*s^45 , (116465883/1361029120*q-61798860402341657/1361029120)*s^45 ), # 24
   ( (-784105141874720768/16526448172540041922855*q-73551314944/664565)*s^45 , (-119260128478157078528/181790929897940461151405*q-204279382016/664565)*s^45 ), # 25
   ( -201326592/664565*s^26 , -33554432/15455*s^26 ), # 26
   ( (-6823589462409216/36358185979588092230281*q-100663296/664565)*s^26 , (-377332243112132608/181790929897940461151405*q-16777216/15455)*s^26 ), # 27
   ( -1316864/664565*s^11 , -15772672/664565*s^11 ), # 28
   ( (-292070259377152/181790929897940461151405*q-658432/664565)*s^11 , (-4117947067994624/181790929897940461151405*q-7886336/664565)*s^11 ), # 29
   ( 4923392/664565*s^13 , -27766784/664565*s^13 ), # 30
   ( (280363090079744/36358185979588092230281*q+2461696/664565)*s^13 , (-7242916151412736/181790929897940461151405*q-13883392/664565)*s^13 ), # 31
   ( (-711243/5316520*q+377398133573097/5316520)*s^52 , (7263537/10633040*q-3854161386388523/10633040)*s^52 ), # 32
   ( (410318542734627864576/181790929897940461151405*q-102545719296/664565)*s^52 , (-757469948309746597888/181790929897940461151405*q-1997420806144/664565)*s^52 ), # 33
   ( 148983/664565 , -1050997/1329130 ), # 34
   ( 1439514140379/6610579269016016769142*q+148983/1329130 , -547827832143703/727163719591761844605620*q-1050997/2658260 ), # 35
   ( (-663072411/348423454720*q+351837965836167769/348423454720)*s^35 , (4469614197/1393693818880*q-2371656460224728663/1393693818880)*s^35 ), # 36
   ( (556780391814397952/36358185979588092230281*q+4294967296/664565)*s^35 , (-3973960469634351104/181790929897940461151405*q-8589934592/664565)*s^35 ), # 37
   ( 119537664/664565*s^20 , -163053568/664565*s^20 ), # 38
   ( (32709433158008832/181790929897940461151405*q+59768832/664565)*s^20 , (-41121543806517248/181790929897940461151405*q-81526784/664565)*s^20 ), # 39
   ( 1375808/664565*s^5 , -1709936/664565*s^5 ), # 40
   ( (363239548610656/181790929897940461151405*q+687904/664565)*s^5 , (-442187887557736/181790929897940461151405*q-854968/664565)*s^5 ), # 41
   ( 271616/60415*s^7 , -2416192/664565*s^7 ), # 42
   ( (788540221257344/181790929897940461151405*q+135808/60415)*s^7 , (-620615997962336/181790929897940461151405*q-1208096/664565)*s^7 ), # 43
   ( (-2606913/34025728*q+1383274212312027/34025728)*s^46 , (37413291/680514560*q-19852154881281289/680514560)*s^46 ), # 44
   ( (114947550197846114304/181790929897940461151405*q+167503724544/664565)*s^46 , (-45987200670705385472/181790929897940461151405*q-17179869184/60415)*s^46 ), # 45
   ( (-2606913/17012864*q+1383274212312027/17012864)*s^48 , (12189363/170128640*q-6467891909860577/170128640)*s^48 ), # 46
   ( (229895100395692228608/181790929897940461151405*q+335007449088/664565)*s^48 , (-3136420567498883072/16526448172540041922855*q-294205259776/664565)*s^48 ), # 47
   ( 536870912/132913*s^29 , -805306368/664565*s^29 ), # 48
   ( (720546538912219136/181790929897940461151405*q+268435456/132913)*s^29 , (-27294357849636864/36358185979588092230281*q-402653184/664565)*s^29 ), # 49
   ( 6045696/132913*s^14 , -5267456/664565*s^14 ), # 50
   ( (722165806964736/16526448172540041922855*q+3022848/132913)*s^14 , (-1168281037508608/181790929897940461151405*q-2633728/664565)*s^14 ), # 51
   ( (-3/4*q+1591853137/4)*s^53 , (571209/5316520*q-303093612844211/5316520)*s^53 ), # 52
   ( (962629219677060530176/181790929897940461151405*q+1946147946496/664565)*s^53 , (30847497784611405824/16526448172540041922855*q-235633082368/132913)*s^53 ), # 53
   ( 119998/132913*s , -2029/664565*s ), # 54
   ( (156750277466137/181790929897940461151405*q+59999/132913)*s , (1596277975553/363581859795880922302810*q-2029/1329130)*s ), # 55
   ( (-320792913/21776465920*q+170218401628806027/21776465920)*s^40 , (-4297317/8710586368*q+2280232515711143/8710586368)*s^40 ), # 56
   ( (18679743837609394176/181790929897940461151405*q+38654705664/664565)*s^40 , (326497439542411264/16526448172540041922855*q-4294967296/664565)*s^40 ), # 57
   ( 771751936/664565*s^25 , 16777216/60415*s^25 ), # 58
   ( (197195608384077824/181790929897940461151405*q+385875968/664565)*s^25 , (64479856879992832/181790929897940461151405*q+8388608/60415)*s^25 ), # 59
   ( 8215552/664565*s^10 , 2790912/664565*s^10 ), # 60
   ( (426398219768320/36358185979588092230281*q+4107776/664565)*s^10 , (773925290043648/181790929897940461151405*q+1395456/664565)*s^10 ), # 61
   ( 12652544/664565*s^12 , 11249664/664565*s^12 ), # 62
   ( (3271004213106688/181790929897940461151405*q+6326272/664565)*s^12 , (3037317556952064/181790929897940461151405*q+5624832/664565)*s^12 ), # 63
   ( (-3152991/10633040*q+1673032871427589/10633040)*s^51 , (-6728583/21266080*q+3570305318704957/21266080)*s^51 ), # 64
   ( (298896352880667656192/181790929897940461151405*q+4294967296/3091)*s^51 , (124136809740420251648/36358185979588092230281*q+416611827712/664565)*s^51 ), # 65
   ( 4294967296/664565*s^32 , 6442450944/664565*s^32 ), # 66
   ( (993490117408587776/181790929897940461151405*q+2147483648/664565)*s^32 , (1888696038240288768/181790929897940461151405*q+3221225472/664565)*s^32 ), # 67
   ( 40763392/664565*s^17 , 80150528/664565*s^17 ), # 68
   ( (10280385951629312/181790929897940461151405*q+20381696/664565)*s^17 , (21494909554819072/181790929897940461151405*q+40075264/664565)*s^17 ), # 69
   ( 427484/664565*s^2 , 901646/664565*s^2 ), # 70
   ( (110546971889434/181790929897940461151405*q+213742/664565)*s^2 , (47378652050009/36358185979588092230281*q+450823/664565)*s^2 ), # 71
   ( 604048/664565*s^4 , 1795912/664565*s^4 ), # 72
   ( (155153999490584/181790929897940461151405*q+302024/664565)*s^4 , (10973188613348/4227696044138150259335*q+897956/664565)*s^4 ), # 73
   ( (-37413291/2722058240*q+19852154881281289/2722058240)*s^43 , (-245966331/5444116480*q+130514091866243449/5444116480)*s^43 ), # 74
   ( (11496800167676346368/181790929897940461151405*q+4294967296/60415)*s^43 , (63222175182761230336/181790929897940461151405*q+21474836480/132913)*s^43 ), # 75
   ( (-12189363/680514560*q+6467891909860577/680514560)*s^45 , (-116465883/1361029120*q+61798860402341657/1361029120)*s^45 ), # 76
   ( (784105141874720768/16526448172540041922855*q+73551314944/664565)*s^45 , (119260128478157078528/181790929897940461151405*q+204279382016/664565)*s^45 ), # 77
   ( 201326592/664565*s^26 , 33554432/15455*s^26 ), # 78
   ( (6823589462409216/36358185979588092230281*q+100663296/664565)*s^26 , (377332243112132608/181790929897940461151405*q+16777216/15455)*s^26 ), # 79
   ( 1316864/664565*s^11 , 15772672/664565*s^11 ), # 80
   ( (292070259377152/181790929897940461151405*q+658432/664565)*s^11 , (4117947067994624/181790929897940461151405*q+7886336/664565)*s^11 ), # 81
   ( -4923392/664565*s^13 , 27766784/664565*s^13 ), # 82
   ( (-280363090079744/36358185979588092230281*q-2461696/664565)*s^13 , (7242916151412736/181790929897940461151405*q+13883392/664565)*s^13 ), # 83
   ( (711243/5316520*q-377398133573097/5316520)*s^52 , (-7263537/10633040*q+3854161386388523/10633040)*s^52 ), # 84
   ( (-410318542734627864576/181790929897940461151405*q+102545719296/664565)*s^52 , (757469948309746597888/181790929897940461151405*q+1997420806144/664565)*s^52 ), # 85
   ( -148983/664565 , 1050997/1329130 ), # 86
   ( -1439514140379/6610579269016016769142*q-148983/1329130 , 547827832143703/727163719591761844605620*q+1050997/2658260 ), # 87
   ( (663072411/348423454720*q-351837965836167769/348423454720)*s^35 , (-4469614197/1393693818880*q+2371656460224728663/1393693818880)*s^35 ), # 88
   ( (-556780391814397952/36358185979588092230281*q-4294967296/664565)*s^35 , (3973960469634351104/181790929897940461151405*q+8589934592/664565)*s^35 ), # 89
   ( -119537664/664565*s^20 , 163053568/664565*s^20 ), # 90
   ( (-32709433158008832/181790929897940461151405*q-59768832/664565)*s^20 , (41121543806517248/181790929897940461151405*q+81526784/664565)*s^20 ), # 91
   ( -1375808/664565*s^5 , 1709936/664565*s^5 ), # 92
   ( (-363239548610656/181790929897940461151405*q-687904/664565)*s^5 , (442187887557736/181790929897940461151405*q+854968/664565)*s^5 ), # 93
   ( -271616/60415*s^7 , 2416192/664565*s^7 ), # 94
   ( (-788540221257344/181790929897940461151405*q-135808/60415)*s^7 , (620615997962336/181790929897940461151405*q+1208096/664565)*s^7 ), # 95
   ( (2606913/34025728*q-1383274212312027/34025728)*s^46 , (-37413291/680514560*q+19852154881281289/680514560)*s^46 ), # 96
   ( (-114947550197846114304/181790929897940461151405*q-167503724544/664565)*s^46 , (45987200670705385472/181790929897940461151405*q+17179869184/60415)*s^46 ), # 97
   ( (2606913/17012864*q-1383274212312027/17012864)*s^48 , (-12189363/170128640*q+6467891909860577/170128640)*s^48 ), # 98
   ( (-229895100395692228608/181790929897940461151405*q-335007449088/664565)*s^48 , (3136420567498883072/16526448172540041922855*q+294205259776/664565)*s^48 ), # 99
   ( -536870912/132913*s^29 , 805306368/664565*s^29 ), # 100
   ( (-720546538912219136/181790929897940461151405*q-268435456/132913)*s^29 , (27294357849636864/36358185979588092230281*q+402653184/664565)*s^29 ), # 101
   ( -6045696/132913*s^14 , 5267456/664565*s^14 ), # 102
   ( (-722165806964736/16526448172540041922855*q-3022848/132913)*s^14 , (1168281037508608/181790929897940461151405*q+2633728/664565)*s^14 ), # 103
  )

Hstable = {
  -1/2: H0,
  1/2: H1,
}
Hstable[3/2] = hullmap(UP0/s,Hstable[1/2])
Hstable[5/2] = hullmap(UP0/s,Hstable[3/2])
Hstable[7/2] = hullmap((33/32)*UP0/s,Hstable[5/2])
for delta in sorted(deltarange):
  if delta > 7/2:
    Hstable[delta] = hullmap(UP0/s,Hstable[delta-1])
for delta in sorted(deltarange):
  if delta < -1/2:
    Hstable[delta] = hullmap(DOWN/s,Hstable[1-delta])

def hol_stablehull():
  result = '(* ----- stable hull *)\n\n'
  result += hol_definehull('H0',H0)
  result += '\n'
  result += hol_definehull('H1',H1)
  result += '\n'
  return result

# ----- scaling initial hull to fit stable hull

stretchprecision = 8192 # XXX

assert initialsteps == 0

stretchlimits = []
for ux,uy in Hinit[0,1/2]:
  if (ux,uy) == (0,0): continue
  stretchlimits += [
    -c/(a*ux+b*uy)
    for a,b,c in constraints(Hstable[1/2])
    if Lsign(a*ux+b*uy) > 0
  ]
stretch = -Lmax(stretchlimits)
stretch = LtoRR(stretch)
stretch = floor(stretchprecision*stretch)/stretchprecision
hol_stretch = hol_QQ(stretch)
hol_invstretch = hol_QQ(1/stretch)

init2stable = prove_inclusion(0,stretch*identity_matrix(2),Hinitname[0,1/2],Hinit[0,1/2],'H1',H1)

if approx:
  savememory = '(* skipping Gc for approx *)'
else:
  savememory = r'''Gc.full_major();;
Gc.compact();;'''

def hol_init2stable():
  return fr'''let init2stable = {init2stable};;

let init2stable_simple = prove(`
  !x:real y:real.
  divsteps_hinit_0_1 x y ==>
  divsteps_H1 (({hol_stretch})*x) (({hol_stretch})*y)
  `,
  REPEAT STRIP_TAC THEN
  note `divsteps_H1 ((({hol_stretch}) * x + (&0) * y) / divsteps_s pow 0) (((&0) * x + ({hol_stretch}) * y) / divsteps_s pow 0)` [init2stable] THEN
  real_linear `((({hol_stretch}) * x + (&0) * y) / divsteps_s pow 0) = ({hol_stretch}) * x` THEN
  real_linear `(((&0) * x + ({hol_stretch}) * y) / divsteps_s pow 0) = ({hol_stretch}) * y` THEN
  ASM_MESON_TAC[]
);;

{savememory}
'''

# ----- stable-hull transitions

h1_contains0 = prove_contains0('H1',H1)

theorem0 = prove_inclusion(1,UP0,'H0',H0,'H1',H1)
theorem1 = prove_inclusion(1,UP1,'H0',H0,'H1',H1)

# trivial: inclusion(1,UP0,'H1',H1,H2) since H2 = UP0*H1/s
theorem3 = prove_inclusion(1,DOWN,'H1',H1,'H1',H1)

# trivial: inclusion(1,UP0,H2,H3) since H3 = UP0*H2/s
theorem5 = prove_inclusion(2,DOWN*UP0,'H1',H1,'H0',H0) # i.e. inclusion(1,DOWN,H2,H0)

# trivial: inclusion(1,UP0,H3,H4) since H4 = UP0*H3/s
# trivial: inclusion(1,DOWN,H3,H_1) since H_1 = DOWN*H3/s

theorem_2 = prove_inclusion(4,UP0*DOWN*UP0*UP0,'H1',H1,'H0',H0) # i.e. inclusion(1,UP0,H_1,H0)
theorem_1 = prove_inclusion(4,UP1*DOWN*UP0*UP0,'H1',H1,'H0',H0) # i.e. inclusion(1,UP1,H_1,H0)

theorem_4scale = prove_inclusion(2,(33/32)*(DOWN*UP0*UP0)^(-1)*UP0*DOWN*UP0*UP0*UP0,'H1',H1,'H1',H1) # i.e. inclusion(1,UP0,H_2,H_1)
theorem_3scale = prove_inclusion(2,(33/32)*(DOWN*UP0*UP0)^(-1)*UP1*DOWN*UP0*UP0*UP0,'H1',H1,'H1',H1) # i.e. inclusion(1,UP1,H_2,H_1)

if 0:
  # these are instead derived from h1shrink; see unscale below
  theorem_4 = prove_inclusion(2,(DOWN*UP0*UP0)^(-1)*UP0*DOWN*UP0*UP0*UP0,'H1',H1,'H1',H1)
  theorem_3 = prove_inclusion(2,(DOWN*UP0*UP0)^(-1)*UP1*DOWN*UP0*UP0*UP0,'H1',H1,'H1',H1)

# redundant because of convexity:
# inclusion(2,(DOWN*UP0*UP0*UP0)^(-1)*UP0*DOWN*UP0*UP0*UP0*UP0,H1,H1) # i.e. inclusion(1,UP0,H_3,H_2)
# inclusion(2,(DOWN*UP0*UP0*UP0)^(-1)*UP1*DOWN*UP0*UP0*UP0*UP0,H1,H1) # i.e. inclusion(1,UP1,H_3,H_2)

# similarly inclusions are trivial or redundant for all other delta

def hol_transitions():
  return fr'''(* ----- stable-hull transitions *)

let h1_contains0 = {h1_contains0};;

{savememory}

let theorem0 =
{theorem0};;

{savememory}

let theorem1 =
{theorem1};;

{savememory}

let theorem3 =
{theorem3};;

{savememory}

let theorem5 =
{theorem5};;

{savememory}

let theorem_2 =
{theorem_2};;

{savememory}

let theorem_1 =
{theorem_1};;

{savememory}

let theorem_4scale =
{theorem_4scale};;

{savememory}

let theorem_3scale =
{theorem_3scale};;

{savememory}

'''

def hol_convexity():
  return r'''(* ----- convexity *)

let ineq_convex = prove(`
  !a b c x0 y0 x1 y1 t:real.
  a*x0+b*y0 <= c ==>
  a*x1+b*y1 <= c ==>
  &0 <= t ==>
  t <= &1 ==>
  a*((&1-t)*x0+t*x1)+b*((&1-t)*y0+t*y1) <= c
  `,
  REPEAT STRIP_TAC THEN
  real_linear `t <= &1 ==> &0 <= &1-t:real` THEN
  note `(&1-t)*(a*x0+b*y0) <= (&1-t)*c:real` [REAL_LE_LMUL] THEN
  note `t*(a*x1+b*y1) <= t*c:real` [REAL_LE_LMUL] THEN
  note `(&1-t)*(a*x0+b*y0)+t*(a*x1+b*y1) <= (&1-t)*c+t*c:real` [REAL_LE_ADD2] THEN
  ASM_REAL_ARITH_TAC
);;

let h1_convex = prove(`
  !x0 y0 x1 y1 t.
  divsteps_H1 x0 y0 ==>
  divsteps_H1 x1 y1 ==>
  &0 <= t ==>
  t <= &1 ==>
  divsteps_H1 ((&1-t)*x0+t*x1) ((&1-t)*y0+t*y1)
  `,
  REWRITE_TAC[divsteps_H1] THEN
  SIMP_TAC[ineq_convex]
);;

let h1_convex_horizontal = prove(`
  !x0 x1 y t.
  divsteps_H1 x0 y ==>
  divsteps_H1 x1 y ==>
  &0 <= t ==>
  t <= &1 ==>
  divsteps_H1 ((&1-t)*x0+t*x1) y
  `,
  MESON_TAC[
    h1_convex;
    REAL_ARITH `y:real = (&1-t)*y+t*y`
  ]
);;

let h1_shrink = prove(`
  !x y t.
  divsteps_H1 x y ==>
  &0 <= t ==>
  t <= &1 ==>
  divsteps_H1 (t*x) (t*y)
  `,
  MESON_TAC[
    h1_contains0;
    h1_convex;
    REAL_ARITH `(&1-t)* &0 + c = c`
  ]
);;

let h1_shrink32 = prove(`
  !x y.
  divsteps_H1 x y ==>
  divsteps_H1 ((&32 / &33)*x) ((&32 / &33)*y)
  `,
  MESON_TAC[
    REAL_ARITH `&0:real <= &32 / &33`;
    REAL_ARITH `&32 / &33 <= &1:real`;
    h1_shrink
  ]
);;

let unscale_4 = prove(`
  (!x:real y:real.
   divsteps_H1 x y ==>
   divsteps_H1 (((&33 / &64) * x + (&33 / &512) * y) / divsteps_s pow 2) (((&0) * x + (&33 / &64) * y) / divsteps_s pow 2)
  ) ==>
  (!x:real y:real.
   divsteps_H1 x y ==>
   divsteps_H1 (((&1 / &2) * x + (&1 / &16) * y) / divsteps_s pow 2) (((&0) * x + (&1 / &2) * y) / divsteps_s pow 2)
  )
  `,
  REPEAT STRIP_TAC THEN
  specialize[`x:real`;`y:real`]h1_shrink32 THEN
  ASM_MESON_TAC[
    REAL_ARITH `((&33 / &64) * ((&32 / &33) * x) + (&33 / &512) * ((&32 / &33) * y)) = ((&1 / &2) * x + (&1 / &16) * y):real`;
    REAL_ARITH `(((&0) * ((&32 / &33) * x) + (&33 / &64) * ((&32 / &33) * y)) / divsteps_s pow 2) = (((&0) * x + (&1 / &2) * y) / divsteps_s pow 2):real`;
  ]
);;

let unscale_3 = prove(`
  (!x:real y:real.
   divsteps_H1 x y ==>
   divsteps_H1 (((&33 / &64) * x + (-- &33 / &512) * y) / divsteps_s pow 2) (((&0) * x + (&33 / &64) * y) / divsteps_s pow 2)
  ) ==>
  (!x:real y:real.
   divsteps_H1 x y ==>
   divsteps_H1 (((&1 / &2) * x + (-- &1 / &16) * y) / divsteps_s pow 2) (((&0) * x + (&1 / &2) * y) / divsteps_s pow 2)
  )
  `,
  REPEAT STRIP_TAC THEN
  specialize[`x:real`;`y:real`]h1_shrink32 THEN
  ASM_MESON_TAC[
    REAL_ARITH `((&33 / &64) * ((&32 / &33) * x) + (-- &33 / &512) * ((&32 / &33) * y)) = ((&1 / &2) * x + (-- &1 / &16) * y):real`;
    REAL_ARITH `(((&0) * ((&32 / &33) * x) + (&33 / &64) * ((&32 / &33) * y)) / divsteps_s pow 2) = (((&0) * x + (&1 / &2) * y) / divsteps_s pow 2):real`;
  ]
);;

let h1_16_lemma1 = prove(`
  !m x y:real. 2 <= m ==>
  (&1 - (&1 / &2 - &2 / &2 pow m)) * ((&1 / &2) * x + (&1 / &16) * y)
  + (&1 / &2 - &2 / &2 pow m) * ((&1 / &2) * x + (-- &1 / &16) * y)
  = ((&1 / &2) * x + (&1 / &2 pow (m + 2)) * y)
  /\ &0 <= &1 / &2 - &2 / &2 pow m
  /\ &1 / &2 - &2 / &2 pow m <= &1
  `,
  REPEAT STRIP_TAC THENL [
    real_linear `(&1 - (&1 / &2 - &2 / &2 pow m)) * ((&1 / &2) * x + (&1 / &16) * y) + (&1 / &2 - &2 / &2 pow m) * ((&1 / &2) * x + (-- &1 / &16) * y) = (&1 / &2) * x + ((&4 / &2 pow m) * (&1 / &16)) * y` THEN
    real_cancel `(&4 / &2 pow m) * (&1 / &16) = &1 / (&2 pow m * &2 pow 2)` THEN
    REWRITE_TAC[REAL_POW_ADD] THEN
    ASM_MESON_TAC[]
  ;
    note `&2 pow 2 <= &2 pow m` [
      REAL_POW_MONO;
      REAL_ARITH `&1 <= &2:real`
    ] THEN
    real_linear `&0:real < &2 pow 2` THEN
    note `inv(&2 pow m) <= inv(&2 pow 2):real` [REAL_LE_INV2] THEN
    ASM_REAL_ARITH_TAC
  ;
    real_linear `&0:real < &2` THEN
    note `&0:real < &2 pow m` [REAL_POW_LT] THEN
    note `&0 < &2 / &2 pow m` [REAL_LT_DIV] THEN
    ASM_REAL_ARITH_TAC
  ]
  );;

let h1_16_lemma1neg = prove(`
  !m x y:real. 2 <= m ==>
  (&1 - (&1 / &2 - &2 / &2 pow m)) * ((&1 / &2) * x + (-- &1 / &16) * y)
  + (&1 / &2 - &2 / &2 pow m) * ((&1 / &2) * x + (&1 / &16) * y)
  = ((&1 / &2) * x - (&1 / &2 pow (m + 2)) * y)
  /\ &0 <= &1 / &2 - &2 / &2 pow m
  /\ &1 / &2 - &2 / &2 pow m <= &1
  `,
  REPEAT STRIP_TAC THENL [
    real_linear `(&1 - (&1 / &2 - &2 / &2 pow m)) * ((&1 / &2) * x + (-- &1 / &16) * y) + (&1 / &2 - &2 / &2 pow m) * ((&1 / &2) * x + (&1 / &16) * y) = (&1 / &2) * x - ((&4 / &2 pow m) * (&1 / &16)) * y` THEN
    real_cancel `(&4 / &2 pow m) * (&1 / &16) = &1 / (&2 pow m * &2 pow 2)` THEN
    REWRITE_TAC[REAL_POW_ADD] THEN
    ASM_MESON_TAC[]
  ;
    note `&2 pow 2 <= &2 pow m` [
      REAL_POW_MONO;
      REAL_ARITH `&1 <= &2:real`
    ] THEN
    real_linear `&0:real < &2 pow 2` THEN
    note `inv(&2 pow m) <= inv(&2 pow 2):real` [REAL_LE_INV2] THEN
    ASM_REAL_ARITH_TAC
  ;
    real_linear `&0:real < &2` THEN
    note `&0:real < &2 pow m` [REAL_POW_LT] THEN
    note `&0 < &2 / &2 pow m` [REAL_LT_DIV] THEN
    ASM_REAL_ARITH_TAC
  ]
  );;

let h1_16_lemma2 = prove(`
  !m x y. 2 <= m ==>
  (&1 - (&1 / &2 - &2 / &2 pow m)) * ((&1 / &2) * x + (&1 / &16) * y) / divsteps_s pow 2
  + (&1 / &2 - &2 / &2 pow m) * ((&1 / &2) * x + (-- &1 / &16) * y) / divsteps_s pow 2
  = ((&1 / &2) * x + (&1 / &2 pow (m + 2)) * y) / divsteps_s pow 2
  /\ &0 <= &1 / &2 - &2 / &2 pow m
  /\ &1 / &2 - &2 / &2 pow m <= &1
  `,
  REPEAT STRIP_TAC THEN
  note `&0 < divsteps_s` [divsteps_s] THEN
  note `&0 < divsteps_s pow 2` [REAL_LT_MUL;REAL_POW_2] THEN
  real_cancel `&0 < divsteps_s pow 2 ==> (&1 - (&1 / &2 - &2 / &2 pow m)) * ((&1 / &2) * x + (&1 / &16) * y) / divsteps_s pow 2 + (&1 / &2 - &2 / &2 pow m) * ((&1 / &2) * x + (-- &1 / &16) * y) / divsteps_s pow 2 = ((&1 - (&1 / &2 - &2 / &2 pow m)) * ((&1 / &2) * x + (&1 / &16) * y) + (&1 / &2 - &2 / &2 pow m) * ((&1 / &2) * x + (-- &1 / &16) * y)) / divsteps_s pow 2` THEN
  ASM_SIMP_TAC[h1_16_lemma1]
);;

let h1_16_lemma2neg = prove(`
  !m x y. 2 <= m ==>
  (&1 - (&1 / &2 - &2 / &2 pow m)) * ((&1 / &2) * x + (-- &1 / &16) * y) / divsteps_s pow 2
  + (&1 / &2 - &2 / &2 pow m) * ((&1 / &2) * x + (&1 / &16) * y) / divsteps_s pow 2
  = ((&1 / &2) * x - (&1 / &2 pow (m + 2)) * y) / divsteps_s pow 2
  /\ &0 <= &1 / &2 - &2 / &2 pow m
  /\ &1 / &2 - &2 / &2 pow m <= &1
  `,
  REPEAT STRIP_TAC THEN
  note `&0 < divsteps_s` [divsteps_s] THEN
  note `&0 < divsteps_s pow 2` [REAL_LT_MUL;REAL_POW_2] THEN
  real_cancel `&0 < divsteps_s pow 2 ==> (&1 - (&1 / &2 - &2 / &2 pow m)) * ((&1 / &2) * x + (-- &1 / &16) * y) / divsteps_s pow 2 + (&1 / &2 - &2 / &2 pow m) * ((&1 / &2) * x + (&1 / &16) * y) / divsteps_s pow 2 = ((&1 - (&1 / &2 - &2 / &2 pow m)) * ((&1 / &2) * x + (-- &1 / &16) * y) + (&1 / &2 - &2 / &2 pow m) * ((&1 / &2) * x + (&1 / &16) * y)) / divsteps_s pow 2` THEN
  ASM_SIMP_TAC[h1_16_lemma1neg]
);;

let h1_16_lemma3 = prove(`
  (!x y. divsteps_H1 x y ==>
  divsteps_H1 (((&1 / &2) * x + (&1 / &16) * y) / divsteps_s pow 2) (((&0) * x + (&1 / &2) * y) / divsteps_s pow 2)
  ) ==>
  (!x y. divsteps_H1 x y ==>
  divsteps_H1 (((&1 / &2) * x + (-- &1 / &16) * y) / divsteps_s pow 2) (((&0) * x + (&1 / &2) * y) / divsteps_s pow 2)
  ) ==>
  !x y m. 2 <= m ==>
  divsteps_H1 x y ==>
  divsteps_H1 (((&1 / &2) * x + (&1 / &2 pow (m + 2)) * y) / divsteps_s pow 2) (((&0) * x + (&1 / &2) * y) / divsteps_s pow 2)
  `,
  MESON_TAC[
    h1_16_lemma2;
    h1_convex_horizontal
  ]);;

let h1_16_lemma3neg = prove(`
  (!x y. divsteps_H1 x y ==>
  divsteps_H1 (((&1 / &2) * x + (&1 / &16) * y) / divsteps_s pow 2) (((&0) * x + (&1 / &2) * y) / divsteps_s pow 2)
  ) ==>
  (!x y. divsteps_H1 x y ==>
  divsteps_H1 (((&1 / &2) * x + (-- &1 / &16) * y) / divsteps_s pow 2) (((&0) * x + (&1 / &2) * y) / divsteps_s pow 2)
  ) ==>
  !x y m. 2 <= m ==>
  divsteps_H1 x y ==>
  divsteps_H1 (((&1 / &2) * x - (&1 / &2 pow (m + 2)) * y) / divsteps_s pow 2) (((&0) * x + (&1 / &2) * y) / divsteps_s pow 2)
  `,
  MESON_TAC[
    h1_16_lemma2neg;
    h1_convex_horizontal
  ]);;

(* ----- unifying the stability theorems *)

let divsteps_W = new_definition `
  !i:int x:real y:real.
  divsteps_W i x y <=>
  if i = -- &1 then
    divsteps_H0 x y
  else if i = -- &2 then
    divsteps_H1 ((x - &2 * y) * (divsteps_s zpow (&1 - i)))
                (x * (divsteps_s zpow (&1 - i)) / (&2 zpow i))
  else if i < -- &2 then
    divsteps_H1 ((&32 / &33) * (x - &2 * y) * (divsteps_s zpow (&1 - i)))
                ((&32 / &33) * x * (divsteps_s zpow (&1 - i)) / (&2 zpow i))
  else if i > &2 then
    divsteps_H1 ((&32 / &33) * x * (divsteps_s zpow i))
                ((&32 / &33) * y * ((&2 * divsteps_s) zpow i))
  else
    divsteps_H1 (x * (divsteps_s zpow i))
                (y * ((&2 * divsteps_s) zpow i))
`;;

let w_transition0 = prove(`
  (!x y. divsteps_H0 x y ==> divsteps_H1 (((&1) * x + (&0) * y) / divsteps_s pow 1) (((&0) * x + (&1 / &2) * y) / divsteps_s pow 1)) ==>
  (!x y. divsteps_H0 x y ==> divsteps_H1 (((&1) * x + (&0) * y) / divsteps_s pow 1) (((&1 / &2) * x + (&1 / &2) * y) / divsteps_s pow 1)) ==>
  (!x y. divsteps_H1 x y ==> divsteps_H1 (((&0) * x + (&1) * y) / divsteps_s pow 1) (((-- &1 / &2) * x + (&1 / &2) * y) / divsteps_s pow 1)) ==>
  (!x y. divsteps_H1 x y ==> divsteps_H0 (((&0) * x + (&1 / &2) * y) / divsteps_s pow 2) (((-- &1 / &2) * x + (&1 / &4) * y) / divsteps_s pow 2)) ==>
  (!x y. divsteps_H1 x y ==> divsteps_H0 (((&0) * x + (&1 / &4) * y) / divsteps_s pow 4) (((-- &1 / &4) * x + (&1 / &16) * y) / divsteps_s pow 4)) ==>
  (!x y. divsteps_H1 x y ==> divsteps_H0 (((&0) * x + (&1 / &4) * y) / divsteps_s pow 4) (((-- &1 / &4) * x + (&3 / &16) * y) / divsteps_s pow 4)) ==>
  (!x y. divsteps_H1 x y ==> divsteps_H1 (((&33 / &64) * x + (&33 / &512) * y) / divsteps_s pow 2) (((&0) * x + (&33 / &64) * y) / divsteps_s pow 2)) ==>
  (!x y. divsteps_H1 x y ==> divsteps_H1 (((&33 / &64) * x + (-- &33 / &512) * y) / divsteps_s pow 2) (((&0) * x + (&33 / &64) * y) / divsteps_s pow 2)) ==>
  !i x y. divsteps_W i x y ==> divsteps_W (&1 + i) (x / divsteps_s) (y / (&2 * divsteps_s))
`,
  REPEAT DISCH_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[divsteps_W] THEN
  note `&0 < divsteps_s` [divsteps_s] THEN
  ASM_CASES_TAC `i:int = -- &1` THENL [
    real_linear `((&1 * x + &0 * y) / divsteps_s pow 1) = (x / divsteps_s * &1)` THEN
    real_cancel `((&0 * x + &1 / &2 * y) / divsteps_s pow 1) = y / (&2 * divsteps_s) * &1` THEN
    ASM_SIMP_TAC[
      INT_ARITH `&1 + -- &1 = &0:int`;
      INT_ARITH `~(&0 = -- &1:int)`;
      INT_ARITH `~(&0 = -- &2:int)`;
      INT_ARITH `~(&0 < -- &2:int)`;
      INT_ARITH `~(&0 < &0:int)`;
      INT_ARITH `~(&0 > &2:int)`;
      REAL_ZPOW_0;
    ] THEN
    ASM_MESON_TAC[]
  ; ALL_TAC
  ] THEN
  ASM_CASES_TAC `i:int = -- &2` THENL [
    real_cancel `&0 < divsteps_s ==> x / divsteps_s = (&0 * ((x - &2 * y) * divsteps_s pow 3) + &1 / &4 * (x * divsteps_s pow 3 / inv (&2 pow 2))) / divsteps_s pow 4` THEN
    real_cancel `&0 < divsteps_s ==> y / (&2 * divsteps_s) = (-- &1 / &4 * ((x - &2 * y) * divsteps_s pow 3) + &1 / &16 * (x * divsteps_s pow 3 / inv (&2 pow 2))) / divsteps_s pow 4` THEN
    ASM_SIMP_TAC[
      INT_ARITH `~(-- &2 = -- &1:int)`;
      INT_ARITH `&1 + -- &2 = -- &1:int`;
      INT_ARITH `-- &2 < &0:int`;
      INT_ARITH `&1 - -- &2 = &3:int`;
      REAL_ZPOW_NEG;
      REAL_ZPOW_NUM
    ]
  ; ALL_TAC
  ] THEN
  ASM_CASES_TAC `i:int = -- &3` THENL [
    real_cancel `&0 < divsteps_s ==> ((x / divsteps_s - &2 * y / (&2 * divsteps_s)) * divsteps_s pow 3) = (((&33 / &64) * (&32 / &33 * (x - &2 * y) * divsteps_s pow 4) + (&33 / &512) * (&32 / &33 * x * divsteps_s pow 4 / inv (&2 pow 3))) / divsteps_s pow 2)` THEN
    real_cancel `&0 < divsteps_s ==> (x / divsteps_s * divsteps_s pow 3 / inv (&2 pow 2)) = (((&0) * (&32 / &33 * (x - &2 * y) * divsteps_s pow 4) + (&33 / &64) * (&32 / &33 * x * divsteps_s pow 4 / inv (&2 pow 3))) / divsteps_s pow 2)` THEN
    ASM_SIMP_TAC[
      INT_ARITH `~(-- &3 = -- &1:int)`;
      INT_ARITH `~(-- &3 = -- &2:int)`;
      INT_ARITH `-- &3 < -- &2:int`;
      INT_ARITH `&1 + -- &3 = -- &2:int`;
      INT_ARITH `~(-- &2 = -- &1:int)`;
      INT_ARITH `&1 - -- &2 = &3:int`;
      INT_ARITH `&1 - -- &3 = &4:int`;
      REAL_ZPOW_NEG;
      REAL_ZPOW_NUM
    ]
  ; ALL_TAC
  ] THEN
  ASM_CASES_TAC `i:int = &2` THENL [
    real_cancel `&0 < divsteps_s ==> &32 / &33 * (x * divsteps_s pow 2) = (&32 / &33 * x / divsteps_s * divsteps_s pow 3)` THEN
    real_cancel `&0 < divsteps_s ==> &32 / &33 * (y * (&2 * divsteps_s) pow 2) = (&32 / &33 * y / (&2 * divsteps_s) * (&2 * divsteps_s) pow 3)` THEN
    ASM_SIMP_TAC[
      INT_ARITH `~(&2 = -- &1:int)`;
      INT_ARITH `~(&2 = -- &2:int)`;
      INT_ARITH `~(&2 < -- &2:int)`;
      INT_ARITH `~(&2 > &2:int)`;
      INT_ARITH `&1 + &2 = &3:int`;
      INT_ARITH `~(&3 = -- &1:int)`;
      INT_ARITH `~(&3 = -- &2:int)`;
      INT_ARITH `~(&3 < -- &2:int)`;
      INT_ARITH `&3 > &2:int`;
      REAL_ZPOW_POW
    ] THEN
    ASM_MESON_TAC[h1_shrink32]
  ; ALL_TAC
  ] THEN
  ASM_CASES_TAC `i:int < -- &2` THENL [
    ASM_SIMP_TAC [
      INT_ARITH `i:int < -- &2 ==> ~(i = -- &1)`;
      INT_ARITH `i:int < -- &2 ==> ~(i = -- &2)`;
      INT_ARITH `i:int < -- &2 ==> ~(&1 + i = -- &1)`;
      INT_ARITH `~(i:int = -- &3) ==> ~(&1 + i = -- &2)`;
      INT_ARITH `i:int < -- &2 /\ ~(i = -- &3) ==> &1 + i < -- &2`;
      INT_ARITH `&1 - (&1 + i:int) = -- i`
    ] THEN
    int_linear `i:int < -- &2 ==> i < &0` THEN
    choosevar `m:num` `i:int = -- &(m + 1)` [int_neg_as_minusnum1] THEN
    real_linear `&0 < divsteps_s ==> ~(divsteps_s = &0)` THEN
    real_linear `~(&2 = &0:real)` THEN
    ASM_SIMP_TAC[
      GSYM INT_OF_NUM_ADD;INT_NEG_NEG;
      INT_ARITH `&1 - --(&m + &1) = &m + &2:int`;
      REAL_ZPOW_NEG;
      REAL_ZPOW_ADD;
      REAL_ZPOW_POW;
      REAL_INV_INV;
    ] THEN
    note `~(m + 1 = 1)` [] THEN
    note `~(m + 1 = 2)` [] THEN
    note `2 <= m` [ARITH_RULE `m + 1 = 1 \/ m + 1 = 2\/ 2 <= m`] THEN
    real_cancel `&0 < divsteps_s ==> ((&1 / &2 * ((&32 / &33) * (x - &2 * y) * divsteps_s pow m * divsteps_s pow 2) + &1 / &2 pow (m + 2) * ((&32 / &33) * x * (divsteps_s pow m * divsteps_s pow 2) / inv (&2 pow m * &2 pow 1))) / divsteps_s pow 2) = (&32 / &33) * ((x / divsteps_s - &2 * y / (&2 * divsteps_s)) * divsteps_s pow m * divsteps_s pow 1)` THEN real_cancel `&0 < divsteps_s ==> ((&0 * ((&32 / &33) * (x - &2 * y) * divsteps_s pow m * divsteps_s pow 2) + &1 / &2 * ((&32 / &33) * x * (divsteps_s pow m * divsteps_s pow 2) /
    inv (&2 pow m * &2 pow 1))) / divsteps_s pow 2) = ((&32 / &33) * x / divsteps_s * (divsteps_s pow m * divsteps_s pow 1) / (&2 pow 1 * inv (&2 pow m * &2 pow 1)))` THEN
    ASM_MESON_TAC[h1_16_lemma3;unscale_4;unscale_3]
  ; ALL_TAC
  ] THEN
  int_linear `~(i < -- &2) /\ ~(i = -- &2) /\ ~(i = -- &1) ==> &0 <= i:int` THEN
  real_linear `&0 < divsteps_s ==> ~(divsteps_s = &0)` THEN
  real_linear `&0 < divsteps_s ==> ~(&2 * divsteps_s = &0)` THEN
  choosevar `m:num` `i:int = &m` [INT_OF_NUM_EXISTS] THEN
  ASM_SIMP_TAC [
    INT_ARITH `&0 <= i:int ==> ~(i = -- &1)`;
    INT_ARITH `&0 <= i:int ==> ~(i = -- &2)`;
    INT_ARITH `&0 <= i:int ==> ~(i < -- &2)`;
    INT_ARITH `&0 <= i:int ==> ~(&1 + i = -- &1)`;
    INT_ARITH `&0 <= i:int ==> ~(&1 + i = -- &2)`;
    INT_ARITH `&0 <= i:int ==> ~(&1 + i < -- &2)`;
    INT_ARITH `&1 - (&1 + i:int) = -- i`;
    REAL_ZPOW_ADD;
    REAL_ZPOW_POW
  ] THEN
  real_cancel `~(divsteps_s = &0) ==> (x / divsteps_s * divsteps_s pow 1 * divsteps_s pow m) = (x * divsteps_s pow m)` THEN
  real_cancel `~(&2 * divsteps_s = &0) ==> (y / (&2 * divsteps_s) * (&2 * divsteps_s) pow 1 * (&2 * divsteps_s) pow m) = (y * (&2 * divsteps_s) pow m)` THEN
  ASM_CASES_TAC `&m:int > &2` THENL [
    ASM_MESON_TAC[INT_ARITH `i:int > &2 ==> &1 + i > &2`]
  ; ASM_MESON_TAC[INT_ARITH `~(i:int > &2) /\ ~(i = &2) ==> ~(&1 + i > &2)`]
  ]
);;

let w_transition1 = prove(`
  (!x y. divsteps_H0 x y ==> divsteps_H1 (((&1) * x + (&0) * y) / divsteps_s pow 1) (((&0) * x + (&1 / &2) * y) / divsteps_s pow 1)) ==>
  (!x y. divsteps_H0 x y ==> divsteps_H1 (((&1) * x + (&0) * y) / divsteps_s pow 1) (((&1 / &2) * x + (&1 / &2) * y) / divsteps_s pow 1)) ==>
  (!x y. divsteps_H1 x y ==> divsteps_H1 (((&0) * x + (&1) * y) / divsteps_s pow 1) (((-- &1 / &2) * x + (&1 / &2) * y) / divsteps_s pow 1)) ==>
  (!x y. divsteps_H1 x y ==> divsteps_H0 (((&0) * x + (&1 / &2) * y) / divsteps_s pow 2) (((-- &1 / &2) * x + (&1 / &4) * y) / divsteps_s pow 2)) ==>
  (!x y. divsteps_H1 x y ==> divsteps_H0 (((&0) * x + (&1 / &4) * y) / divsteps_s pow 4) (((-- &1 / &4) * x + (&1 / &16) * y) / divsteps_s pow 4)) ==>
  (!x y. divsteps_H1 x y ==> divsteps_H0 (((&0) * x + (&1 / &4) * y) / divsteps_s pow 4) (((-- &1 / &4) * x + (&3 / &16) * y) / divsteps_s pow 4)) ==>
  (!x y. divsteps_H1 x y ==> divsteps_H1 (((&33 / &64) * x + (&33 / &512) * y) / divsteps_s pow 2) (((&0) * x + (&33 / &64) * y) / divsteps_s pow 2)) ==>
  (!x y. divsteps_H1 x y ==> divsteps_H1 (((&33 / &64) * x + (-- &33 / &512) * y) / divsteps_s pow 2) (((&0) * x + (&33 / &64) * y) / divsteps_s pow 2)) ==>
  !i x y. divsteps_W i x y ==>
    if i < &0 then
      divsteps_W (&1 + i) (x / divsteps_s) ((y + x) / (&2 * divsteps_s))
    else
      divsteps_W (--i) (y / divsteps_s) ((y - x) / (&2 * divsteps_s))
  `,
  REPEAT DISCH_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[divsteps_W] THEN
  note `&0 < divsteps_s` [divsteps_s] THEN
  ASM_CASES_TAC `i:int = -- &1` THENL [
    real_linear `((&1 * x + &0 * y) / divsteps_s pow 1) = (x / divsteps_s * &1)` THEN
    real_cancel `((&1 / &2 * x + &1 / &2 * y) / divsteps_s pow 1) = ((y + x) / (&2 * divsteps_s) * &1)` THEN
    ASM_SIMP_TAC[
      INT_ARITH `-- &1 < &0:int`;
      INT_ARITH `&1 + -- &1 = &0:int`;
      INT_ARITH `~(&0 = -- &1:int)`;
      INT_ARITH `~(&0 = -- &2:int)`;
      INT_ARITH `~(&0 < -- &2:int)`;
      INT_ARITH `~(&0 < &0:int)`;
      INT_ARITH `~(&0 > &2:int)`;
      REAL_ZPOW_0;
    ] THEN
    ASM_MESON_TAC[]
  ; ALL_TAC
  ] THEN
  ASM_CASES_TAC `i:int = -- &2` THENL [
    real_cancel `&0 < divsteps_s ==> ((-- &1 / &4 * ((x - &2 * y) * divsteps_s pow 3) + &3 / &16 * (x * divsteps_s pow 3 / inv (&2 pow 2))) / divsteps_s pow 4) = ((-- &1 / &4 * ((x - &2 * y)) + &3 / &16 * (x / inv (&2 pow 2))) / divsteps_s)` THEN
    real_cancel `((-- &1 / &4 * ((x - &2 * y)) + &3 / &16 * (x / inv (&2 pow 2))) / divsteps_s) = ((y + x) / (&2 * divsteps_s))` THEN
    real_cancel `&0 < divsteps_s ==> ((&0 * ((x - &2 * y) * divsteps_s pow 3) + &1 / &4 * (x * divsteps_s pow 3 / inv (&2 pow 2))) / divsteps_s pow 4) = (x / divsteps_s)` THEN
    ASM_SIMP_TAC[
      INT_ARITH `~(-- &2 = -- &1:int)`;
      INT_ARITH `&1 + -- &2 = -- &1:int`;
      INT_ARITH `-- &2 < &0:int`;
      INT_ARITH `&1 - -- &2 = &3:int`;
      REAL_ZPOW_NEG;
      REAL_ZPOW_NUM
    ] THEN
    ASM_MESON_TAC[]
  ; ALL_TAC
  ] THEN
  ASM_CASES_TAC `i:int = -- &3` THENL [
    real_cancel `&0 < divsteps_s ==> ((x / divsteps_s - &2 * (y + x) / (&2 * divsteps_s)) * divsteps_s pow 3) = (((&33 / &64) * (&32 / &33 * (x - &2 * y) * divsteps_s pow 4) + (-- &33 / &512) * (&32 / &33 * x * divsteps_s pow 4 / inv (&2 pow 3))) / divsteps_s pow 2)` THEN
    real_cancel `&0 < divsteps_s ==> (x / divsteps_s * divsteps_s pow 3 / inv (&2 pow 2)) = (((&0) * (&32 / &33 * (x - &2 * y) * divsteps_s pow 4) + (&33 / &64) * (&32 / &33 * x * divsteps_s pow 4 / inv (&2 pow 3))) / divsteps_s pow 2)` THEN
    ASM_SIMP_TAC[
      INT_ARITH `-- &3 < &0:int`;
      INT_ARITH `~(-- &3 = -- &1:int)`;
      INT_ARITH `~(-- &3 = -- &2:int)`;
      INT_ARITH `-- &3 < -- &2:int`;
      INT_ARITH `&1 + -- &3 = -- &2:int`;
      INT_ARITH `~(-- &2 = -- &1:int)`;
      INT_ARITH `&1 - -- &2 = &3:int`;
      INT_ARITH `&1 - -- &3 = &4:int`;
      REAL_ZPOW_NEG;
      REAL_ZPOW_NUM
    ] THEN
    ASM_MESON_TAC[]
  ; ALL_TAC
  ] THEN
  ASM_CASES_TAC `i:int = &0` THENL [
    ASM_SIMP_TAC[
      INT_ARITH `~(&0 = -- &1:int)`;
      INT_ARITH `~(&0 < &0:int)`;
      INT_ARITH `~(&0 = -- &2:int)`;
      INT_ARITH `~(&0 < -- &2:int)`;
      INT_ARITH `~(&0 > &2:int)`;
      INT_ARITH `-- &0 = &0:int`;
      REAL_ZPOW_0
    ] THEN
    REWRITE_TAC[REAL_ARITH `x * &1 = x`] THEN
    real_linear `(&0 * x + &1 * y) / divsteps_s pow 1 = y / divsteps_s` THEN
    real_cancel `(-- &1 / &2 * x + &1 / &2 * y) / divsteps_s pow 1 = (y - x) / (&2 * divsteps_s)` THEN
    ASM_MESON_TAC[]
  ; ALL_TAC
  ] THEN
  ASM_CASES_TAC `i:int = &1` THENL [
    ASM_SIMP_TAC[
      INT_ARITH `~(&1:int = -- &1)`;
      INT_ARITH `~(&1:int = -- &2)`;
      INT_ARITH `~(&1:int < -- &2)`;
      INT_ARITH `~(&1:int > &2)`;
      INT_ARITH `~(&1:int < &0)`;
      REAL_ZPOW_1
    ] THEN
    real_cancel `&0 < divsteps_s ==> ((&0 * (x * divsteps_s) + &1 / &2 * (y * &2 * divsteps_s)) / divsteps_s pow 2) = (y / divsteps_s)` THEN
    real_cancel `&0 < divsteps_s ==> ((-- &1 / &2 * (x * divsteps_s) + &1 / &4 * (y * &2 * divsteps_s)) / divsteps_s pow 2) = ((y - x) / (&2 * divsteps_s))` THEN
    ASM_MESON_TAC[]
  ; ALL_TAC
  ] THEN
  ASM_CASES_TAC `i:int = &2` THENL [
    ASM_SIMP_TAC[
      INT_ARITH `~(&2 < &0:int)`;
      INT_ARITH `~(&2 = -- &1:int)`;
      INT_ARITH `~(&2 = -- &2:int)`;
      INT_ARITH `~(&2 < -- &2:int)`;
      INT_ARITH `~(&2 > &2:int)`;
      INT_ARITH `~(-- &2 = -- &1:int)`;
      INT_ARITH `&1 - -- &2:int = &3`;
      REAL_ZPOW_POW
    ] THEN
    real_cancel `&0 < divsteps_s ==> (x * divsteps_s pow 2) = ((y / divsteps_s - &2 * (y - x) / (&2 * divsteps_s)) * divsteps_s pow 3)` THEN
    real_cancel `&0 < divsteps_s ==> (y * (&2 * divsteps_s) pow 2) = (y / divsteps_s * divsteps_s pow 3 / inv (&2 pow 2))` THEN
    ASM_MESON_TAC[]
  ; ALL_TAC
  ] THEN
  ASM_CASES_TAC `i:int < -- &2` THENL [
    int_linear `i:int < -- &2 ==> i < &0` THEN
    ASM_SIMP_TAC [
      INT_ARITH `i:int < -- &2 ==> ~(i = -- &1)`;
      INT_ARITH `i:int < -- &2 ==> ~(i = -- &2)`;
      INT_ARITH `i:int < -- &2 ==> ~(&1 + i = -- &1)`;
      INT_ARITH `~(i:int = -- &3) ==> ~(&1 + i = -- &2)`;
      INT_ARITH `i:int < -- &2 /\ ~(i = -- &3) ==> &1 + i < -- &2`;
      INT_ARITH `&1 - (&1 + i:int) = -- i`
    ] THEN
    choosevar `m:num` `i:int = -- &(m + 1)` [int_neg_as_minusnum1] THEN
    real_linear `&0 < divsteps_s ==> ~(divsteps_s = &0)` THEN
    real_linear `~(&2 = &0:real)` THEN
    ASM_SIMP_TAC[
      GSYM INT_OF_NUM_ADD;INT_NEG_NEG;
      INT_ARITH `&1 - --(&m + &1) = &m + &2:int`;
      REAL_ZPOW_NEG;
      REAL_ZPOW_ADD;
      REAL_ZPOW_POW;
      REAL_INV_INV;
    ] THEN
    note `~(m + 1 = 1)` [] THEN
    note `~(m + 1 = 2)` [] THEN
    note `2 <= m` [ARITH_RULE `m + 1 = 1 \/ m + 1 = 2\/ 2 <= m`] THEN
    real_cancel `&0 < divsteps_s ==> ((&1 / &2 * ((&32 / &33) * (x - &2 * y) * divsteps_s pow m * divsteps_s pow 2) - &1 / &2 pow (m + 2) * ((&32 / &33) * x * (divsteps_s pow m * divsteps_s pow 2) / inv (&2 pow m * &2 pow 1))) / divsteps_s pow 2) = (&32 / &33) * ((x / divsteps_s - &2 * (y + x) / (&2 * divsteps_s)) * divsteps_s pow m * divsteps_s pow 1)` THEN
    real_cancel `&0 < divsteps_s ==> ((&0 * ((&32 / &33) * (x - &2 * y) * divsteps_s pow m * divsteps_s pow 2) + &1 / &2 * ((&32 / &33) * x * (divsteps_s pow m * divsteps_s pow 2) / inv (&2 pow m * &2 pow 1))) / divsteps_s pow 2) = (&32 / &33) * (x / divsteps_s * (divsteps_s pow m * divsteps_s pow 1) / (&2 pow 1 * inv (&2 pow m * &2 pow 1)))` THEN
    ASM_MESON_TAC[h1_16_lemma3neg;unscale_4;unscale_3]
  ; ALL_TAC
  ] THEN
  int_linear `~(i < -- &2) /\ ~(i = -- &2) /\ ~(i = -- &1) ==> &0 <= i:int` THEN
  ASM_SIMP_TAC[
    INT_ARITH `&0 <= i:int ==> ~(i < &0)`;
    INT_ARITH `&0 <= i:int ==> ~(i = -- &1)`;
    INT_ARITH `&0 <= i:int ==> ~(i = -- &2)`;
    INT_ARITH `&0 <= i:int ==> ~(i < -- &2)`;
    INT_ARITH `&0 <= i:int /\ ~(i = &0) /\ ~(i = &1) /\ ~(i = &2) ==> i > &2`;
    INT_ARITH `~(i:int = &1) ==> ~(--i = -- &1)`;
    INT_ARITH `~(i:int = &2) ==> ~(--i = -- &2)`;
    INT_ARITH `&0 <= i:int /\ ~(i = &0) /\ ~(i = &1) /\ ~(i = &2) ==> --i < -- &2`;
  ] THEN
  real_linear `&0 < divsteps_s ==> ~(divsteps_s = &0)` THEN
  real_linear `&0 < divsteps_s ==> ~(&2 * divsteps_s = &0)` THEN
  choosevar `m:num` `i:int = &m` [INT_OF_NUM_EXISTS] THEN
  ASM_SIMP_TAC[
    INT_ARITH `&1 - -- &m:int = &1 + &m`;
    REAL_ZPOW_ADD;
    REAL_ZPOW_POW
  ] THEN
  real_cancel `&0 < divsteps_s ==> (x * divsteps_s pow m) = ((y / divsteps_s - &2 * (y - x) / (&2 * divsteps_s)) * divsteps_s pow 1 * divsteps_s pow m)` THEN
  note `(&2 * divsteps_s) pow m = &2 pow m * divsteps_s pow m` [REAL_POW_MUL] THEN
  real_cancel `&0 < divsteps_s ==> (y * &2 pow m * divsteps_s pow m) = (y / divsteps_s * (divsteps_s pow 1 * divsteps_s pow m) / inv (&2 pow m))` THEN
  ASM_MESON_TAC[]
);;

'''

# ----- outer hull

H1xmax = Lmax([x for (x,y) in H1])
H1ymax = Lmax([y for (x,y) in H1])
outerstretchx = ceil(stretchprecision*LtoRR(H1xmax))/stretchprecision
outerstretchy = ceil(stretchprecision*LtoRR(H1ymax))/stretchprecision

Houter = (
  (-outerstretchx,-outerstretchy),
  (outerstretchx,-outerstretchy),
  (outerstretchx,outerstretchy),
  (-outerstretchx,outerstretchy),
)

theoremouter = prove_inclusion(0,identity_matrix(2),'H1',H1,'Houter',Houter)

def hol_outer():
  return fr'''(* ----- outer hull *)

{hol_definehull('Houter',Houter)}

let theoremouter =
{theoremouter};;

let theoremouter_simple = prove(`
  !x:real y:real.
  divsteps_H1 x y ==>
  divsteps_Houter x y
  `,
  REPEAT STRIP_TAC THEN
  note `divsteps_Houter (((&1) * x + (&0) * y) / divsteps_s pow 0) (((&0) * x + (&1) * y) / divsteps_s pow 0)` [theoremouter] THEN
  real_linear `(((&1) * x + (&0) * y) / divsteps_s pow 0) = x` THEN
  real_linear `(((&0) * x + (&1) * y) / divsteps_s pow 0) = y` THEN
  ASM_MESON_TAC[]
);;

{savememory}

'''

# ----- lattice constraints

def exact_latticescale():
  limits = [
    -c/(a+b)
    for a,b,c in constraints(H1)
    if Lsign(a+b) > 0
  ]
  latticestretch = -Lmax(limits)

  delta = 1/2
  while True:
    if Lsign(H1xmax/(2*s^2)^(delta-1/2)-latticestretch) < 0: break
    absf = 1
    while True:
      if Lsign(absf*latticestretch-H1xmax) > 0: break
      g = 1
      while True:
        if Lsign(g*latticestretch-H1ymax) > 0: break
        for fsign in 1,-1:
          f = fsign*absf
          fover = f/2^(delta-1/2)
          newlimits = [
            -c/(a*fover+b*g)
            for a,b,c in constraints(H1)
            if Lsign(a*fover+b*g) > 0
          ]
          newlatticestretch = -Lmax(newlimits)/(2*s^2)^(delta-1/2)
          if Lsign(newlatticestretch-latticestretch) > 0:
            latticestretch = newlatticestretch
        g += 1
      absf += 2
    delta += 1

  return 1/latticestretch

latticescale = LtoRR(exact_latticescale())
latticescale = floor(stretchprecision*latticescale)/stretchprecision
hol_latticescale = hol_QQ(latticescale)

fuzziness = latticescale*stretch
hol_fuzziness = hol_QQ(fuzziness)

def prove_lattice_onedelta(delta):
  result = ''
  i = ZZ(delta-1/2)
  assert i >= 0

  fudge = 32/33 if i > 2 else 1

  xscale = fudge*(s^2)^i/latticescale
  yscale = fudge*(2*s^2)^i/latticescale

  # considering lattice points (x,y)
  # with (x*xscale,y*yscale) in H1

  xmax = floor(LtoRR(outerstretchx/xscale))
  ymax = floor(LtoRR(outerstretchy/yscale))
  xmin = -xmax
  ymin = -ymax

  xcases = ' \\/ '.join('x:real = -- &%d'%(-x) if x < 0 else 'x:real = &%d'%x for x in range(xmin,xmax+1))
  mcases = ' \\/ '.join('m = %d'%m for m in range(0,xmax+1))
  absxcases = ' \\/ '.join('abs(x):real = &%d'%m for m in range(0,xmax+1))
  pmxcases = ' \\/ '.join('x:real = &%d \\/ --x = &%d'%(m,m) for m in range(0,xmax+1))
  xpmcases = ' \\/ '.join('x:real = &%d \\/ x = -- &%d'%(m,m) for m in range(0,xmax+1))

  ycases = ' \\/ '.join('y:real = -- &%d'%(-y) if y < 0 else 'y:real = &%d'%y for y in range(ymin,ymax+1))
  nonzeroycases = ' \\/ '.join('y:real = -- &%d'%(-y) if y < 0 else 'y:real = &%d'%y for y in range(ymin,ymax+1) if y != 0)
  ncases = ' \\/ '.join('n = %d'%n for n in range(0,ymax+1))
  absycases = ' \\/ '.join('abs(y):real = &%d'%n for n in range(0,ymax+1))
  pmycases = ' \\/ '.join('y:real = &%d \\/ --y = &%d'%(m,m) for m in range(0,ymax+1))
  ypmcases = ' \\/ '.join('y:real = &%d \\/ y = -- &%d'%(m,m) for m in range(0,ymax+1))

  hol_fudge = hol_QQ(fudge)
  hol_xscale,hol_yscale = map(hol_L_divsteps,(xscale,yscale))

  cases = []
  for y in range(ymin,ymax+1):
    if y == 0: continue
    for x in range(xmin,xmax+1):
      lemmaname = 'lemma_%d_%d_%d' % (i,x-xmin,y-ymin)
      result += 'let %s = %s in\n' % (lemmaname,prove_notcontains('H1',H1,x*xscale,y*yscale))
      cases += [lemmaname]
      cases += ['REAL_ARITH `%s = (%s) * (%s):real`' % (hol_L(x*xscale),hol_ZZ(x),hol_L(xscale))]
      cases += ['REAL_ARITH `%s = (%s) * (%s):real`' % (hol_L(y*yscale),hol_ZZ(y),hol_L(yscale))]
  cases = ';\n    '.join(cases)

  Ax = constraints(Houter)[1][0]
  Cx = constraints(Houter)[1][2]
  CAx = Cx/Ax
  assert CAx == outerstretchx
  By = constraints(Houter)[2][1]
  Cy = constraints(Houter)[2][2]
  CBy = Cy/By
  assert CBy == outerstretchy
  Ax,Cx,CAx,By,Cy,CBy = map(hol_QQ,(Ax,Cx,CAx,By,Cy,CBy))

  result += fr'''let lattice_{i}_split = prove(`
  !x y.
  integer(x) ==>
  integer(y) ==>
  divsteps_Houter (x * {hol_xscale}) (y * {hol_yscale}) ==>
  ({xcases}) /\
  ({ycases})
  `,
  REWRITE_TAC[divsteps_Houter] THEN
  {divsteps_qs_setup} THEN
  REPEAT STRIP_TAC THENL [
    {specialize_qs}({indent(prove_positive(xscale))}) THEN
    {specialize_qs}({indent(prove_positive(xscale*(xmax+1)-outerstretchx))}) THEN
    real_linear `&0:real < {hol_L_divsteps(xscale*(xmax+1)-outerstretchx)} ==> {CAx} < ({hol_ZZ(xmax+1)})*({hol_xscale})` THEN
    note `({CAx}) / ({hol_xscale}) < {hol_ZZ(xmax+1)}:real` [real_lt_ldiv] THEN

    note `({Ax}) * x * ({hol_xscale}) <= {Cx}` [REAL_ARITH `t + &0 * u = t:real`] THEN
    real_linear `({Ax}) * x * ({hol_xscale}) <= {Cx} ==> x * ({hol_xscale}) <= ({CAx}):real` THEN
    note `x:real <= ({CAx}) / ({hol_xscale})` [REAL_LE_RDIV] THEN
    note `x:real < {hol_ZZ(xmax+1)}` [REAL_LET_TRANS] THEN

    note `-- ({Ax}) * x * ({hol_xscale}) <= {Cx}` [REAL_ARITH `t + &0 * u = t:real`] THEN
    real_linear `-- ({Ax}) * x * ({hol_xscale}) <= {Cx} ==> -- x * ({hol_xscale}) <= ({CAx}):real` THEN
    note `-- x:real <= ({CAx}) / ({hol_xscale})` [REAL_LE_RDIV] THEN
    note `-- x:real < {hol_ZZ(xmax+1)}` [REAL_LET_TRANS] THEN
    note `{hol_ZZ(xmin-1)} < x:real` [REAL_LT_NEG2;REAL_NEG_NEG] THEN

    note `abs(x):real < {hol_ZZ(xmax+1)}` [REAL_BOUNDS_LT] THEN
    choosevar `m:num` `abs(x) = &m:real` [integer] THEN
    note `m < {xmax+1}` [REAL_OF_NUM_LT] THEN
    num_linear `m < {xmax+1} ==> {mcases}` THEN
    note `{absxcases}` [] THEN
    note `{pmxcases}` [real_abs] THEN
    note `{xpmcases}` [REAL_NEG_NEG] THEN
    ASM_MESON_TAC[REAL_NEG_0]
  ;
    {specialize_qs}({indent(prove_positive(yscale))}) THEN
    {specialize_qs}({indent(prove_positive(yscale*(ymax+1)-outerstretchy))}) THEN
    real_linear `&0:real < {hol_L_divsteps(yscale*(ymax+1)-outerstretchy)} ==> {CBy} < ({hol_ZZ(ymax+1)})*({hol_yscale})` THEN
    note `({CBy}) / ({hol_yscale}) < {hol_ZZ(ymax+1)}:real` [real_lt_ldiv] THEN

    note `({By}) * y * ({hol_yscale}) <= {Cy}` [REAL_ARITH `&0 * u + t = t:real`] THEN
    real_linear `({By}) * y * ({hol_yscale}) <= {Cy} ==> y * ({hol_yscale}) <= ({CBy}):real` THEN
    note `y:real <= ({CBy}) / ({hol_yscale})` [REAL_LE_RDIV] THEN
    note `y:real < {hol_ZZ(ymax+1)}` [REAL_LET_TRANS] THEN

    note `-- ({By}) * y * ({hol_yscale}) <= {Cy}` [REAL_ARITH `&0 * u + t = t:real`] THEN
    real_linear `-- ({By}) * y * ({hol_yscale}) <= {Cy} ==> -- y * ({hol_yscale}) <= ({CBy}):real` THEN
    note `-- y:real <= ({CBy}) / ({hol_yscale})` [REAL_LE_RDIV] THEN
    note `-- y:real < {hol_ZZ(ymax+1)}` [REAL_LET_TRANS] THEN
    note `{hol_ZZ(ymin-1)} < y:real` [REAL_LT_NEG2;REAL_NEG_NEG] THEN

    note `abs(y):real < {hol_ZZ(ymax+1)}` [REAL_BOUNDS_LT] THEN
    choosevar `n:num` `abs(y) = &n:real` [integer] THEN
    note `n < {ymax+1}` [REAL_OF_NUM_LT] THEN
    num_linear `n < {ymax+1} ==> {ncases}` THEN
    note `{absycases}` [] THEN
    note `{pmycases}` [real_abs] THEN
    note `{ypmcases}` [REAL_NEG_NEG] THEN
    ASM_MESON_TAC[REAL_NEG_0]
  ]
) in
'''

  result += fr'''let lattice_{i}_followup = prove(`
  !x y.
  ({xcases}) ==>
  ({nonzeroycases}) ==>
  ~(divsteps_H1 (x * ({hol_xscale})) (y * ({hol_yscale})))
  `,
  MESON_TAC[
    {cases}
  ]
) in
'''

  result += fr'''let lattice_{i}_yzero = prove(`
  !x y.
  integer(x) ==>
  integer(y) ==>
  divsteps_Houter (x * ({hol_xscale})) (y * ({hol_yscale})) ==>
  divsteps_H1 (x * ({hol_xscale})) (y * ({hol_yscale})) ==>
  y = &0
  `,
  REPEAT STRIP_TAC THEN
  note `({xcases}) /\ ({ycases})` [lattice_{i}_split] THEN
  ASM_MESON_TAC[lattice_{i}_followup]
) in
'''

  if approx:
    subst_s = f'({hol_L(s)})'
    start = f'REPEAT STRIP_TAC THEN\n  note `divsteps_s = {hol_L(s)}` [divsteps_s]'
  else:
    subst_s = 'divsteps_s'
    start = 'REPEAT STRIP_TAC'

  result += fr'''prove(`
  (!x:real y:real.
   divsteps_H1 x y ==>
   divsteps_Houter x y
  ) ==>
  !x y u.
  integer(x) ==>
  integer(y) ==>
  ~(y = &0) ==>
  &0 < u ==>
  divsteps_H1 (x * ({hol_fudge}) * ((divsteps_s pow 2) pow {i}) / u) (y * ({hol_fudge}) * ((&2 * divsteps_s pow 2) pow {i}) / u) ==> 
  {hol_latticescale} < u
  `,
  {start} THEN
  ASM_CASES_TAC `u:real <= {hol_latticescale}` THENL [
    real_linear `u:real <= {hol_latticescale} ==> u / ({hol_latticescale}) <= &1` THEN
    real_linear `&0 < u:real ==> &0 <= u / ({hol_latticescale})` THEN
    specialize[`x * ({hol_fudge}) * ((divsteps_s pow 2) pow {i}) / u`;`y * ({hol_fudge}) * ((&2 * divsteps_s pow 2) pow {i}) / u`;`u:real / ({hol_latticescale})`]h1_shrink THEN
    real_cancel `&0 < u ==> u / ({hol_latticescale}) * (x * ({hol_fudge}) * (({subst_s} pow 2) pow {i}) / u) = x * {hol_xscale}` THEN
    real_cancel `&0 < u ==> u / ({hol_latticescale}) * (y * ({hol_fudge}) * ((&2 * {subst_s} pow 2) pow {i}) / u) = y * {hol_yscale}` THEN
    note `divsteps_H1 (x * {hol_xscale}) (y * {hol_yscale})` [] THEN
    note `divsteps_Houter (x * {hol_xscale}) (y * {hol_yscale})` [] THEN
    ASM_MESON_TAC[lattice_{i}_yzero]
  ;
    ASM_REAL_ARITH_TAC
  ]
)'''

  return result

def prove_lattice_bigdelta():
  fudge = 32/33

  mcutoff = 0
  while outerstretchy*latticescale >= LtoRR(fudge*(2*s^2)^mcutoff):
    mcutoff += 1
  yscale = fudge*(2*y^2)^mcutoff/latticescale

  hol_fudge = hol_QQ(fudge)
  hol_yscale = hol_QQxy_divsteps(yscale)

  By = constraints(Houter)[2][1]
  Cy = constraints(Houter)[2][2]
  CBy = Cy/By
  assert CBy == outerstretchy
  By,Cy,CBy = map(hol_QQ,(By,Cy,CBy))

  result = fr'''prove(`
  (!x:real y:real.
   divsteps_H1 x y ==>
   divsteps_Houter x y
  ) ==>
  !m x y u.
  integer(y) ==>
  ~(y = &0) ==>
  &0 < u ==>
  {mcutoff} <= m ==>
  divsteps_H1 (x * ({hol_fudge}) * ((divsteps_s pow 2) pow m) / u) (y * ({hol_fudge}) * ((&2 * divsteps_s pow 2) pow m) / u) ==> 
  {hol_latticescale} < u
  `,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[divsteps_Houter] THEN
  ASM_CASES_TAC `u:real <= {hol_latticescale}` THENL [
    {divsteps_qs_setup} THEN
    num_linear `{mcutoff} <= m ==> m = {mcutoff} + (m - {mcutoff})` THEN
    {specialize_qs}({indent(indent(prove_positive_poly(yscale)))}) THEN
    {specialize_qs}({indent(indent(prove_positive_poly(yscale-outerstretchy)))}) THEN
    real_linear `&0:real < {hol_QQxy_divsteps(yscale-outerstretchy)} ==> {CBy} < {hol_yscale}` THEN
    {specialize_qs}({indent(indent(prove_positive_poly(2*y*y-1)))}) THEN
    real_linear `&0:real < {hol_QQxy_divsteps(2*y*y-1)} ==> &1 <= &2 * divsteps_s pow 2` THEN
    note `&1 <= (&2 * divsteps_s pow 2) pow (m - {mcutoff})` [REAL_POW_LE_1] THEN
    note `&1 <= (&2 * divsteps_s pow 2) pow {mcutoff}` [REAL_POW_LE_1] THEN
    real_linear `&1 <= (&2 * divsteps_s pow 2) pow {mcutoff} ==> &0 < (&2 * divsteps_s pow 2) pow {mcutoff}` THEN
    note `(&2 * divsteps_s pow 2) pow m = (&2 * divsteps_s pow 2) pow {mcutoff} * (&2 * divsteps_s pow 2) pow (m - {mcutoff})` [REAL_POW_ADD] THEN
    real_linear `u:real <= {hol_latticescale} ==> u / ({hol_latticescale}) <= &1` THEN
    real_linear `&0 < u:real ==> &0 <= u / ({hol_latticescale})` THEN
    specialize[`x * ({hol_fudge}) * ((divsteps_s pow 2) pow m) / u`;`y * ({hol_fudge}) * ((&2 * divsteps_s pow 2) pow m) / u`;`u:real / ({hol_latticescale})`]h1_shrink THEN
    real_cancel `&0 < u ==> u / ({hol_latticescale}) * (x * ({hol_fudge}) * ((divsteps_s pow 2) pow m) / u) = x * ({hol_fudge}) * ((divsteps_s pow 2) pow m) / ({hol_latticescale})` THEN
    real_cancel `&0 < u ==> u / ({hol_latticescale}) * (y * ({hol_fudge}) * ((&2 * divsteps_s pow 2) pow m) / u) = y * ({hol_fudge}) * ((&2 * divsteps_s pow 2) pow m) / ({hol_latticescale})` THEN
    note `divsteps_H1 (x * ({hol_fudge}) * ((divsteps_s pow 2) pow m) / ({hol_latticescale})) (y * ({hol_fudge}) * ((&2 * divsteps_s pow 2) pow m) / ({hol_latticescale}))` [] THEN
    note `divsteps_Houter (x * ({hol_fudge}) * ((divsteps_s pow 2) pow m) / ({hol_latticescale})) (y * ({hol_fudge}) * ((&2 * divsteps_s pow 2) pow m) / ({hol_latticescale}))` [] THEN

    note `&0 * (x * ({hol_fudge}) * ((divsteps_s pow 2) pow m) / ({hol_latticescale})) + ({By}) * (y * ({hol_fudge}) * ((&2 * divsteps_s pow 2) pow m) / ({hol_latticescale})) <= {Cy}` [divsteps_Houter] THEN
    note `({By}) * (y * ({hol_fudge}) * ((&2 * divsteps_s pow 2) pow m) / ({hol_latticescale})) <= {Cy}` [REAL_ARITH `&0 * u + t = t:real`] THEN
    real_linear `({By}) * (y * ({hol_fudge}) * ((&2 * divsteps_s pow 2) pow m) / ({hol_latticescale})) <= {Cy} ==> ((y) * ({hol_fudge}) * ((&2 * divsteps_s pow 2) pow m) / ({hol_latticescale})) <= ({CBy}):real` THEN
    note `((y) * ({hol_fudge}) * ((&2 * divsteps_s pow 2) pow {mcutoff} * (&2 * divsteps_s pow 2) pow (m - {mcutoff})) / ({hol_latticescale})) <= ({CBy}):real` [] THEN
    note `((y) * ({hol_fudge}) * ((&2 * divsteps_s pow 2) pow {mcutoff} * (&2 * divsteps_s pow 2) pow (m - {mcutoff})) / ({hol_latticescale})) < ({hol_yscale}):real` [REAL_LET_TRANS] THEN
    real_linear `((y) * ({hol_fudge}) * ((&2 * divsteps_s pow 2) pow {mcutoff} * (&2 * divsteps_s pow 2) pow (m - {mcutoff})) / ({hol_latticescale})) < ({hol_yscale}):real ==> (y) * ((&2 * divsteps_s pow 2) pow {mcutoff} * (&2 * divsteps_s pow 2) pow (m - {mcutoff})) < (&2 * divsteps_s pow 2) pow {mcutoff}` THEN
    note `y < &1:real` [real_lt_rdiv_one_extra] THEN
    
    note `&0 * (x * ({hol_fudge}) * ((divsteps_s pow 2) pow m) / ({hol_latticescale})) + -- ({By}) * (y * ({hol_fudge}) * ((&2 * divsteps_s pow 2) pow m) / ({hol_latticescale})) <= {Cy}` [divsteps_Houter] THEN
    note `-- ({By}) * (y * ({hol_fudge}) * ((&2 * divsteps_s pow 2) pow m) / ({hol_latticescale})) <= {Cy}` [REAL_ARITH `&0 * u + t = t:real`] THEN
    real_linear `-- ({By}) * (y * ({hol_fudge}) * ((&2 * divsteps_s pow 2) pow m) / ({hol_latticescale})) <= {Cy} ==> ((-- y) * ({hol_fudge}) * ((&2 * divsteps_s pow 2) pow m) / ({hol_latticescale})) <= ({CBy}):real` THEN
    note `((--y) * ({hol_fudge}) * ((&2 * divsteps_s pow 2) pow {mcutoff} * (&2 * divsteps_s pow 2) pow (m - {mcutoff})) / ({hol_latticescale})) <= ({CBy}):real` [] THEN
    note `((--y) * ({hol_fudge}) * ((&2 * divsteps_s pow 2) pow {mcutoff} * (&2 * divsteps_s pow 2) pow (m - {mcutoff})) / ({hol_latticescale})) < ({hol_yscale}):real` [REAL_LET_TRANS] THEN
    real_linear `((--y) * ({hol_fudge}) * ((&2 * divsteps_s pow 2) pow {mcutoff} * (&2 * divsteps_s pow 2) pow (m - {mcutoff})) / ({hol_latticescale})) < ({hol_yscale}):real ==> (--y) * ((&2 * divsteps_s pow 2) pow {mcutoff} * (&2 * divsteps_s pow 2) pow (m - {mcutoff})) < (&2 * divsteps_s pow 2) pow {mcutoff}` THEN
    note `--y < &1:real` [real_lt_rdiv_one_extra] THEN
    note `-- &1:real < y` [REAL_LT_NEG2;REAL_NEG_NEG] THEN
    
    note `abs(y):real < &1` [REAL_BOUNDS_LT] THEN
    choosevar `n:num` `abs(y) = &n:real` [integer] THEN
    note `n < 1` [REAL_OF_NUM_LT] THEN
    num_linear `n < 1 ==> n = 0` THEN
    note `abs(y) = &0:real` [] THEN
    real_linear `abs(y) = &0:real ==> y = &0` THEN
    ASM_MESON_TAC[]
  ;
    ASM_REAL_ARITH_TAC
  ]
)'''

  return result

def prove_lattice():
  fudge = 32/33
  hol_fudge = hol_QQ(fudge)

  unhandled = ['&0 <= i:int']
  result = ''
  bigproof = []

  i = 0
  while outerstretchy*latticescale >= LtoRR((32/33)*(2*s^2)^i):
    delta = i+1/2
    result += f'let lattice_{i} = {prove_lattice_onedelta(delta)} in\n'

    if i == 0:
      bigproof += [fr'''ASM_CASES_TAC `i = &0:int` THENL [
  note `divsteps_H1 (x / t * divsteps_s zpow i) (y / t * (&2 * divsteps_s) zpow i)` [
    INT_ARITH `~(&0 = -- &1:int)`;
    INT_ARITH `~(&0 = -- &2:int)`;
    INT_ARITH `~(&0 < -- &2:int)`;
    INT_ARITH `~(&0 > &2:int)`;
  ] THEN
  note `divsteps_s zpow i = divsteps_s pow 0` [REAL_ZPOW_POW] THEN
  note `(&2 * divsteps_s) zpow i = (&2 * divsteps_s) pow 0` [REAL_ZPOW_POW] THEN
  note `divsteps_H1 (x / t * divsteps_s pow 0) (y / t * (&2 * divsteps_s) pow 0)` [] THEN
  real_linear `x / t * divsteps_s pow 0 = x * &1 * divsteps_s pow 2 pow 0 / t` THEN
  real_linear `y / t * (&2 * divsteps_s) pow 0 = y * &1 * (&2 * divsteps_s pow 2) pow 0 / t` THEN
  note `divsteps_H1 (x * &1 * divsteps_s pow 2 pow 0 / t) (y * &1 * (&2 * divsteps_s pow 2) pow 0 / t)` [] THEN
  note `{hol_latticescale} < t:real` [lattice_0] THEN
  real_linear `{hol_latticescale} < t:real ==> {hol_latticescale} < t * divsteps_s pow 0` THEN
  ASM_MESON_TAC[]
; ALL_TAC ]''']

    if i == 1:
      bigproof += [fr'''ASM_CASES_TAC `i = &1:int` THENL [
  note `divsteps_H1 (x / t * divsteps_s zpow i) (y / t * (&2 * divsteps_s) zpow i)` [
    INT_ARITH `~(&1 = -- &1:int)`;
    INT_ARITH `~(&1 = -- &2:int)`;
    INT_ARITH `~(&1 < -- &2:int)`;
    INT_ARITH `~(&1 > &2:int)`;
  ] THEN
  note `divsteps_s zpow i = divsteps_s pow 1` [REAL_ZPOW_POW] THEN
  note `(&2 * divsteps_s) zpow i = (&2 * divsteps_s) pow 1` [REAL_ZPOW_POW] THEN
  note `divsteps_H1 (x / t * divsteps_s pow 1) (y / t * (&2 * divsteps_s) pow 1)` [] THEN
  real_cancel `x / t * divsteps_s pow 1 = x * &1 * divsteps_s pow 2 pow 1 / (t * divsteps_s)` THEN
  real_cancel `y / t * (&2 * divsteps_s) pow 1 = y * &1 * (&2 * divsteps_s pow 2) pow 1 / (t * divsteps_s)` THEN
  note `divsteps_H1 (x * &1 * divsteps_s pow 2 pow 1 / (t * divsteps_s)) (y * &1 * (&2 * divsteps_s pow 2) pow 1 / (t * divsteps_s))` [] THEN
  note `&0 < divsteps_s` [divsteps_s] THEN
  note `&0 < t * divsteps_s` [REAL_LT_MUL] THEN
  note `{hol_latticescale} < t * divsteps_s` [lattice_1] THEN
  real_linear `{hol_latticescale} < t * divsteps_s ==> {hol_latticescale} < t * divsteps_s pow 1` THEN
  ASM_MESON_TAC[]
; ALL_TAC ]''']

    assert i <= 1 # XXX
    unhandled += [f'~(i = &{i}:int)']

    i += 1

  mcutoff = i
  mcutoff3 = max(mcutoff,3)

  result += f'let lattice_bigdelta = {prove_lattice_bigdelta()} in\n'

  bigproof += [fr'''ASM_CASES_TAC `&{mcutoff3} <= i:int` THENL [
  note `divsteps_H1 (({hol_fudge}) * x / t * divsteps_s zpow i) (({hol_fudge}) * y / t * (&2 * divsteps_s) zpow i)` [
    INT_ARITH `&{mcutoff3} <= i:int ==> ~(i = -- &1)`;
    INT_ARITH `&{mcutoff3} <= i:int ==> ~(i = -- &2)`;
    INT_ARITH `&{mcutoff3} <= i:int ==> ~(i < -- &2)`;
    INT_ARITH `&{mcutoff3} <= i:int ==> i > &2`;
  ] THEN
  int_linear `&{mcutoff3} <= i:int ==> &{mcutoff} <= i:int` THEN
  choosevar `m:num` `i:int = &m` [INT_OF_NUM_EXISTS] THEN
  note `divsteps_H1 (({hol_fudge}) * x / t * divsteps_s zpow (&m)) (({hol_fudge}) * y / t * (&2 * divsteps_s) zpow (&m))` [] THEN
  note `divsteps_H1 (({hol_fudge}) * x / t * divsteps_s pow m) (({hol_fudge}) * y / t * (&2 * divsteps_s) pow m)` [REAL_ZPOW_POW] THEN
  real_cancel `({hol_fudge}) * x / t * divsteps_s pow m = x * {hol_fudge} * divsteps_s pow m pow 2 / (t * divsteps_s pow m)` THEN
  note `({hol_fudge}) * x / t * divsteps_s pow m = x * {hol_fudge} * divsteps_s pow (m * 2) / (t * divsteps_s pow m)` [REAL_POW_POW] THEN
  note `({hol_fudge}) * x / t * divsteps_s pow m = x * {hol_fudge} * divsteps_s pow (2 * m) / (t * divsteps_s pow m)` [MULT_SYM] THEN
  note `({hol_fudge}) * x / t * divsteps_s pow m = x * {hol_fudge} * divsteps_s pow 2 pow m / (t * divsteps_s pow m)` [REAL_POW_POW] THEN
  note `&0 < divsteps_s` [divsteps_s] THEN
  note `&0 < divsteps_s pow m` [REAL_POW_LT] THEN
  real_cancel `&0 < divsteps_s pow m ==> ({hol_fudge}) * y / t * (&2 * divsteps_s) pow m = y * {hol_fudge} * ((&2 * divsteps_s) pow m * divsteps_s pow m) / (t * divsteps_s pow m)` THEN
  specialize[`&2 * divsteps_s`;`divsteps_s`;`m:num`]REAL_POW_MUL THEN
  real_linear `(&2 * divsteps_s) * divsteps_s = &2 * divsteps_s pow 2` THEN
  note `({hol_fudge}) * y / t * (&2 * divsteps_s) pow m = y * {hol_fudge} * (&2 * divsteps_s pow 2) pow m / (t * divsteps_s pow m)` [] THEN
  note `divsteps_H1 (x * {hol_fudge} * divsteps_s pow 2 pow m / (t * divsteps_s pow m)) (y * {hol_fudge} * (&2 * divsteps_s pow 2) pow m / (t * divsteps_s pow m))` [] THEN
  note `{mcutoff} <= m` [INT_OF_NUM_LE] THEN
  note `&0 < divsteps_s` [divsteps_s] THEN
  note `&0 < divsteps_s pow m` [REAL_POW_LT] THEN
  note `&0 < t * divsteps_s pow m` [REAL_LT_MUL] THEN
  note `{hol_latticescale} < t * divsteps_s pow m` [lattice_bigdelta] THEN
  ASM_MESON_TAC[REAL_ZPOW_POW]
; ALL_TAC ]''']
  unhandled += [f'~(&{mcutoff3} <= i:int)']

  hol_unhandled = ' /\\ '.join(unhandled)

  # XXX: merge this with previous case

  bigproof += [fr'''int_linear `{hol_unhandled} ==> &{mcutoff} <= i:int` THEN
  note `divsteps_H1 (x / t * divsteps_s zpow i) (y / t * (&2 * divsteps_s) zpow i)` [
    INT_ARITH `{hol_unhandled} ==> ~(i = -- &1)`;
    INT_ARITH `{hol_unhandled} ==> ~(i = -- &2)`;
    INT_ARITH `{hol_unhandled} ==> ~(i < -- &2)`;
    INT_ARITH `{hol_unhandled} ==> ~(i > &2)`;
  ] THEN
  real_linear `&0:real <= {hol_fudge}` THEN
  real_linear `{hol_fudge} <= &1:real` THEN
  note `divsteps_H1 (({hol_fudge}) * (x / t * divsteps_s zpow i)) (({hol_fudge}) * (y / t * (&2 * divsteps_s) zpow i))` [h1_shrink] THEN
  real_linear `(({hol_fudge}) * (x / t * divsteps_s zpow i)) = (({hol_fudge}) * x / t * divsteps_s zpow i)` THEN
  real_linear `(({hol_fudge}) * (y / t * (&2 * divsteps_s) zpow i)) = (({hol_fudge}) * y / t * (&2 * divsteps_s) zpow i)` THEN
  note `divsteps_H1 (({hol_fudge}) * x / t * divsteps_s zpow i) (({hol_fudge}) * y / t * (&2 * divsteps_s) zpow i)` [] THEN
  choosevar `m:num` `i:int = &m` [INT_OF_NUM_EXISTS] THEN
  note `divsteps_H1 (({hol_fudge}) * x / t * divsteps_s zpow (&m)) (({hol_fudge}) * y / t * (&2 * divsteps_s) zpow (&m))` [] THEN
  note `divsteps_H1 (({hol_fudge}) * x / t * divsteps_s pow m) (({hol_fudge}) * y / t * (&2 * divsteps_s) pow m)` [REAL_ZPOW_POW] THEN
  real_cancel `({hol_fudge}) * x / t * divsteps_s pow m = x * {hol_fudge} * divsteps_s pow m pow 2 / (t * divsteps_s pow m)` THEN
  note `({hol_fudge}) * x / t * divsteps_s pow m = x * {hol_fudge} * divsteps_s pow (m * 2) / (t * divsteps_s pow m)` [REAL_POW_POW] THEN
  note `({hol_fudge}) * x / t * divsteps_s pow m = x * {hol_fudge} * divsteps_s pow (2 * m) / (t * divsteps_s pow m)` [MULT_SYM] THEN
  note `({hol_fudge}) * x / t * divsteps_s pow m = x * {hol_fudge} * divsteps_s pow 2 pow m / (t * divsteps_s pow m)` [REAL_POW_POW] THEN
  note `&0 < divsteps_s` [divsteps_s] THEN
  note `&0 < divsteps_s pow m` [REAL_POW_LT] THEN
  real_cancel `&0 < divsteps_s pow m ==> ({hol_fudge}) * y / t * (&2 * divsteps_s) pow m = y * {hol_fudge} * ((&2 * divsteps_s) pow m * divsteps_s pow m) / (t * divsteps_s pow m)` THEN
  specialize[`&2 * divsteps_s`;`divsteps_s`;`m:num`]REAL_POW_MUL THEN
  real_linear `(&2 * divsteps_s) * divsteps_s = &2 * divsteps_s pow 2` THEN
  note `({hol_fudge}) * y / t * (&2 * divsteps_s) pow m = y * {hol_fudge} * (&2 * divsteps_s pow 2) pow m / (t * divsteps_s pow m)` [] THEN
  note `divsteps_H1 (x * {hol_fudge} * divsteps_s pow 2 pow m / (t * divsteps_s pow m)) (y * {hol_fudge} * (&2 * divsteps_s pow 2) pow m / (t * divsteps_s pow m))` [] THEN
  note `{mcutoff} <= m` [INT_OF_NUM_LE] THEN
  note `&0 < divsteps_s` [divsteps_s] THEN
  note `&0 < divsteps_s pow m` [REAL_POW_LT] THEN
  note `&0 < t * divsteps_s pow m` [REAL_LT_MUL] THEN
  note `{hol_latticescale} < t * divsteps_s pow m` [lattice_bigdelta] THEN
  ASM_MESON_TAC[REAL_ZPOW_POW]''']

  bigproof = ' THEN\n  '.join(bigproof)

  result += fr'''prove(`
  (!x:real y:real.
   divsteps_H1 x y ==>
   divsteps_Houter x y
  ) ==>
  !i x y t.
  &0 <= i ==>
  integer(x) ==>
  integer(y) ==>
  ~(y = &0) ==>
  &0 < t ==>
  divsteps_W i (x/t) (y/t) ==>
  {hol_latticescale} < t * divsteps_s zpow i
  `,
  REWRITE_TAC[divsteps_W] THEN
  REPEAT STRIP_TAC THEN
  {bigproof}
)'''

  return result

latticetheorem = prove_lattice()

def hol_latticetheorem():
  return fr'''(* ----- latticetheorem *)

let latticetheorem =
{latticetheorem};;

{savememory}

'''

# ----- main inductive arguments

def prove_iteration_stability():
  return r'''prove(`
  (!x y. divsteps_H0 x y ==> divsteps_H1 (((&1) * x + (&0) * y) / divsteps_s pow 1) (((&0) * x + (&1 / &2) * y) / divsteps_s pow 1)) ==>
  (!x y. divsteps_H0 x y ==> divsteps_H1 (((&1) * x + (&0) * y) / divsteps_s pow 1) (((&1 / &2) * x + (&1 / &2) * y) / divsteps_s pow 1)) ==>
  (!x y. divsteps_H1 x y ==> divsteps_H1 (((&0) * x + (&1) * y) / divsteps_s pow 1) (((-- &1 / &2) * x + (&1 / &2) * y) / divsteps_s pow 1)) ==>
  (!x y. divsteps_H1 x y ==> divsteps_H0 (((&0) * x + (&1 / &2) * y) / divsteps_s pow 2) (((-- &1 / &2) * x + (&1 / &4) * y) / divsteps_s pow 2)) ==>
  (!x y. divsteps_H1 x y ==> divsteps_H0 (((&0) * x + (&1 / &4) * y) / divsteps_s pow 4) (((-- &1 / &4) * x + (&1 / &16) * y) / divsteps_s pow 4)) ==>
  (!x y. divsteps_H1 x y ==> divsteps_H0 (((&0) * x + (&1 / &4) * y) / divsteps_s pow 4) (((-- &1 / &4) * x + (&3 / &16) * y) / divsteps_s pow 4)) ==>
  (!x y. divsteps_H1 x y ==> divsteps_H1 (((&33 / &64) * x + (&33 / &512) * y) / divsteps_s pow 2) (((&0) * x + (&33 / &64) * y) / divsteps_s pow 2)) ==>
  (!x y. divsteps_H1 x y ==> divsteps_H1 (((&33 / &64) * x + (-- &33 / &512) * y) / divsteps_s pow 2) (((&0) * x + (&33 / &64) * y) / divsteps_s pow 2)) ==>
  !i:num->int f:num->real g:num->real u:real.
  i(0) = &0 ==>
  (!n. (i(n+1) = &1 + i(n) /\ f(n+1) = f(n) /\ g(n+1) = g(n) / &2)
    \/ (if i(n) < &0 
        then i(n+1) = &1 + i(n) /\ f(n+1) = f(n) /\ g(n+1) = (g(n)+f(n)) / &2
        else i(n+1) = -- i(n) /\ f(n+1) = g(n) /\ g(n+1) = (g(n)-f(n)) / &2)
  ) ==>
  &0 < u ==>
  divsteps_H1 (f(0)/u) (g(0)/u) ==>
  !m. divsteps_W (i(m)) (f(m)/(u * divsteps_s pow m)) (g(m)/(u * divsteps_s pow m))
  `,
  REPEAT DISCH_TAC THEN
  REPEAT GEN_TAC THEN
  REPEAT DISCH_TAC THEN
  INDUCT_TAC THENL [
    REPEAT STRIP_TAC THEN
    note `divsteps_s zpow &0 = &1` [REAL_ZPOW_0] THEN
    note `(&2 * divsteps_s) zpow &0 = &1` [REAL_ZPOW_0] THEN
    real_cancel `divsteps_s zpow &0 = &1 ==> f(0) / u = (f(0) / u) * divsteps_s zpow &0` THEN
    real_cancel `(&2 * divsteps_s) zpow &0 = &1 ==> g(0) / u = (g(0) / u) * (&2 * divsteps_s) zpow &0` THEN
    note `divsteps_H1 ((f(0) / u) * divsteps_s zpow &0) ((g(0) / u) * (&2 * divsteps_s) zpow &0)` [] THEN
    note `divsteps_W (&0) (f(0)/u) (g(0)/u)` [
      divsteps_W;
      INT_ARITH `~(&0:int = -- &1)`;
      INT_ARITH `~(&0:int = -- &2)`;
      INT_ARITH `~(&0:int < -- &2)`;
      INT_ARITH `~(&0:int > &2)`;
    ] THEN
    real_linear `u * divsteps_s pow 0 = u` THEN
    ASM_MESON_TAC[]
  ;
    REWRITE_TAC[ARITH_RULE `SUC m = m + 1`] THEN
    twocases `i(m:num) < &0:int \/ ~(i(m) < &0)` [] THENL [
      twocases `(i(m+1) = &1 + i(m):int /\ f(m+1) = f(m) /\ g(m+1) = g(m) / &2) \/ (i(m+1) = &1 + i(m) /\ f(m+1) = f(m) /\ g(m+1) = (g(m)+f(m)) / &2)` [] THENL [
        note `divsteps_W (&1 + i(m)) ((f m / (u * divsteps_s pow m)) / divsteps_s) ((g m / (u * divsteps_s pow m)) / (&2 * divsteps_s))` [w_transition0] THEN
        real_cancel `((f m / (u * divsteps_s pow m)) / divsteps_s) = f(m) / (u * divsteps_s pow (m+1))` THEN
        real_cancel `((g m / (u * divsteps_s pow m)) / (&2 * divsteps_s)) = g(m) / &2 / (u * divsteps_s pow (m+1))` THEN
        ASM_MESON_TAC[]
      ;
        note `divsteps_W (&1 + i(m)) ((f m / (u * divsteps_s pow m)) / divsteps_s) ((g m / (u * divsteps_s pow m) + f m / (u * divsteps_s pow m)) / (&2 * divsteps_s))` [w_transition1] THEN
        real_cancel `(f(m) / (u * divsteps_s pow m) / divsteps_s) = (f(m) / (u * divsteps_s pow (m + 1)))` THEN
        real_cancel `((g m / (u * divsteps_s pow m) + f m / (u * divsteps_s pow m)) / (&2 * divsteps_s)) = (((g(m) + f(m)) / &2) / (u * divsteps_s pow (m + 1)))` THEN
        ASM_MESON_TAC[]
      ]
    ;
      twocases `(i(m+1) = &1 + i(m):int /\ f(m+1) = f(m) /\ g(m+1) = g(m) / &2) \/ (i(m+1) = -- i(m) /\ f(m+1) = g(m) /\ g(m+1) = (g(m)-f(m)) / &2)` [] THENL [
        note `divsteps_W (&1 + i(m)) ((f m / (u * divsteps_s pow m)) / divsteps_s) ((g m / (u * divsteps_s pow m)) / (&2 * divsteps_s))` [w_transition0] THEN
        real_cancel `((f m / (u * divsteps_s pow m)) / divsteps_s) = f(m) / (u * divsteps_s pow (m+1))` THEN
        real_cancel `((g m / (u * divsteps_s pow m)) / (&2 * divsteps_s)) = g(m) / &2 / (u * divsteps_s pow (m+1))` THEN
        note `divsteps_W (i(m+1)) (f m / (u * divsteps_s pow m) / divsteps_s) (g m / (u * divsteps_s pow m) / (&2 * divsteps_s))` [] THEN
        note `divsteps_W (i(m+1)) (f(m) / (u * divsteps_s pow (m+1))) (g m / (u * divsteps_s pow m) / (&2 * divsteps_s))` [] THEN
        note `divsteps_W (i(m+1)) (f(m) / (u * divsteps_s pow (m+1))) (g(m) / &2 / (u * divsteps_s pow (m+1)))` [] THEN
        note `divsteps_W (i(m+1)) (f(m+1) / (u * divsteps_s pow (m+1))) (g(m) / &2 / (u * divsteps_s pow (m+1)))` [] THEN
        note `divsteps_W (i(m+1)) (f(m+1) / (u * divsteps_s pow (m+1))) (g(m+1) / (u * divsteps_s pow (m+1)))` [] THEN
        ASM_MESON_TAC[]
      ;
        note `divsteps_W (-- i(m)) ((g m / (u * divsteps_s pow m)) / divsteps_s) ((g m / (u * divsteps_s pow m) - f m / (u * divsteps_s pow m)) / (&2 * divsteps_s))` [w_transition1] THEN
        real_cancel `(g(m) / (u * divsteps_s pow (m + 1))) = (g(m) / (u * divsteps_s pow m) / divsteps_s)` THEN
        real_cancel `(((g(m) - f(m)) / &2) / (u * divsteps_s pow (m + 1))) = ((g(m) / (u * divsteps_s pow m) - f m / (u * divsteps_s pow m)) / (&2 * divsteps_s))` THEN
        note `divsteps_W (-- i(m)) (g(m) / (u * divsteps_s pow (m + 1))) ((g m / (u * divsteps_s pow m) - f m / (u * divsteps_s pow m)) / (&2 * divsteps_s))` [] THEN
        note `divsteps_W (-- i(m)) (g(m) / (u * divsteps_s pow (m + 1))) (((g(m) - f(m)) / &2) / (u * divsteps_s pow (m + 1)))` [] THEN
        note `divsteps_W (i(m+1)) (g(m) / (u * divsteps_s pow (m + 1))) (((g(m) - f(m)) / &2) / (u * divsteps_s pow (m + 1)))` [] THEN
        note `divsteps_W (i(m+1)) (f(m+1) / (u * divsteps_s pow (m + 1))) (((g(m) - f(m)) / &2) / (u * divsteps_s pow (m + 1)))` [] THEN
        ASM_MESON_TAC[]
      ]
    ]
  ]
)'''

def prove_iteration_sizebound():
  # XXX: use latticescale

  return fr'''prove(`
  (!x y. divsteps_H1 x y ==> divsteps_Houter x y) ==>
  (!x y. divsteps_H0 x y ==> divsteps_H1 (((&1) * x + (&0) * y) / divsteps_s pow 1) (((&0) * x + (&1 / &2) * y) / divsteps_s pow 1)) ==>
  (!x y. divsteps_H0 x y ==> divsteps_H1 (((&1) * x + (&0) * y) / divsteps_s pow 1) (((&1 / &2) * x + (&1 / &2) * y) / divsteps_s pow 1)) ==>
  (!x y. divsteps_H1 x y ==> divsteps_H1 (((&0) * x + (&1) * y) / divsteps_s pow 1) (((-- &1 / &2) * x + (&1 / &2) * y) / divsteps_s pow 1)) ==>
  (!x y. divsteps_H1 x y ==> divsteps_H0 (((&0) * x + (&1 / &2) * y) / divsteps_s pow 2) (((-- &1 / &2) * x + (&1 / &4) * y) / divsteps_s pow 2)) ==>
  (!x y. divsteps_H1 x y ==> divsteps_H0 (((&0) * x + (&1 / &4) * y) / divsteps_s pow 4) (((-- &1 / &4) * x + (&1 / &16) * y) / divsteps_s pow 4)) ==>
  (!x y. divsteps_H1 x y ==> divsteps_H0 (((&0) * x + (&1 / &4) * y) / divsteps_s pow 4) (((-- &1 / &4) * x + (&3 / &16) * y) / divsteps_s pow 4)) ==>
  (!x y. divsteps_H1 x y ==> divsteps_H1 (((&33 / &64) * x + (&33 / &512) * y) / divsteps_s pow 2) (((&0) * x + (&33 / &64) * y) / divsteps_s pow 2)) ==>
  (!x y. divsteps_H1 x y ==> divsteps_H1 (((&33 / &64) * x + (-- &33 / &512) * y) / divsteps_s pow 2) (((&0) * x + (&33 / &64) * y) / divsteps_s pow 2)) ==>
  !i:num->int f:num->real g:num->real u:real.
  i(0) = &0 ==>
  (!n. (i(n+1) = &1 + i(n) /\ f(n+1) = f(n) /\ g(n+1) = g(n) / &2)
    \/ (if i(n) < &0 
        then i(n+1) = &1 + i(n) /\ f(n+1) = f(n) /\ g(n+1) = (g(n)+f(n)) / &2
        else i(n+1) = -- i(n) /\ f(n+1) = g(n) /\ g(n+1) = (g(n)-f(n)) / &2)
  ) ==>
  &0 < u ==>
  divsteps_H1 (f(0)/u) (g(0)/u) ==>
  (!n. integer(f(n))) ==>
  (!n. integer(g(n))) ==>
  !m.
    (!n. n <= m ==> ~(g(n) = &0)) ==>
    {hol_latticescale} < u * divsteps_s zpow (&m + if i(m) < &0 then --i(m) - &1 else i(m))
  `,
  REPEAT DISCH_TAC THEN
  REPEAT GEN_TAC THEN
  REPEAT DISCH_TAC THEN
  note `&0 < divsteps_s` [divsteps_s] THEN
  real_linear `&0 < divsteps_s ==> ~(divsteps_s = &0)` THEN
  INDUCT_TAC THENL [
    ASSUME_TAC(SPEC`0`(UNDISCH_ALL(SPECL[`i:num->int`;`f:num->real`;`g:num->real`;`u:real`](UNDISCH_ALL(iteration_stability))))) THEN
    STRIP_TAC THEN
    num_linear `0 <= 0` THEN
    note `~(g(0) = &0:real)` [] THEN
    int_linear `&0 <= &0:int` THEN
    note `integer(f(0))` [] THEN
    note `integer(g(0))` [] THEN
    real_linear `u * divsteps_s pow 0 = u` THEN
    note `&0 < u * divsteps_s pow 0` [] THEN
    note `divsteps_W (&0) (f(0)/(u*divsteps_s pow 0)) (g(0)/(u*divsteps_s pow 0))` [] THEN
    specialize[`&0:int`;`f(0):real`;`g(0):real`;`u * divsteps_s pow 0`](UNDISCH_ALL latticetheorem) THEN
    note `{hol_latticescale} < u * divsteps_s zpow &0` [] THEN
    int_linear `~(&0 < &0:int)` THEN
    int_linear `&0 + &0 = &0:int` THEN
    ASM_SIMP_TAC[]
  ;
    REWRITE_TAC[ARITH_RULE `SUC m = m + 1`] THEN
    ASSUME_TAC(SPEC`m+1`(UNDISCH_ALL(SPECL[`i:num->int`;`f:num->real`;`g:num->real`;`u:real`](UNDISCH_ALL(iteration_stability))))) THEN
    STRIP_TAC THEN
    twocases `~(i(m+1):int < &0) \/ i(m+1) < &0` [] THENL [
      int_linear `~(i(m+1):int < &0) ==> &0 <= i(m+1)` THEN
      num_linear `&0 <= &(m+1):int` THEN
      note `integer(f(m+1))` [] THEN
      note `integer(g(m+1))` [] THEN
      note `~(g(m+1) = &0:real)` [ARITH_RULE `m+1 <= m+1`] THEN
      note `&0 < u * divsteps_s pow (m+1)` [REAL_POW_LT;REAL_LT_MUL] THEN
      ASSUME_TAC(SPEC`m+1`(UNDISCH_ALL(SPECL[`i:num->int`;`f:num->real`;`g:num->real`;`u:real`](UNDISCH_ALL(iteration_stability))))) THEN
      specialize[`i(m+1):int`;`f(m+1):real`;`g(m+1):real`;`u * divsteps_s pow (m+1)`](UNDISCH_ALL latticetheorem) THEN
      note `{hol_latticescale} < (u * divsteps_s zpow (&(m+1))) * divsteps_s zpow (i(m+1))` [REAL_ZPOW_POW] THEN
      real_linear `(u * divsteps_s zpow (&(m+1))) * divsteps_s zpow (i(m+1)) = u * divsteps_s zpow (&(m+1)) * divsteps_s zpow (i(m+1))` THEN
      note `{hol_latticescale} < u * divsteps_s zpow (&(m+1)) * divsteps_s zpow (i(m+1))` [] THEN
      note `divsteps_s zpow (&(m+1)) * divsteps_s zpow (i(m+1)) = divsteps_s zpow (&(m+1) + i(m+1))` [REAL_ZPOW_ADD] THEN
      note `{hol_latticescale} < u * divsteps_s zpow (&(m+1) + i(m+1))` [] THEN
      ASM_MESON_TAC[]
    ;
      note `!n. n <= m:num ==> ~(g(n) = &0:real)` [ARITH_RULE `n <= m ==> n <= m+1`] THEN
      note `{hol_latticescale} < u * divsteps_s zpow (&m + (if i m < &0 then --i m - &1 else i m))` [] THEN
      twocases `i(m+1):int = &1 + i(m) \/ (~(i(m) < &0) /\ i(m+1) = --i(m))` [] THENL [
        int_linear `i(m+1):int = &1 + i(m) /\ i(m+1) < &0 ==> i(m) < &0` THEN
        note `{hol_latticescale} < u * divsteps_s zpow (&m + --i m - &1)` [] THEN
        num_linear `&(m+1) = &m + &1:int` THEN
        int_linear `&m + --i(m) - &1 = (&m + &1) + --(&1 + i(m)) - &1:int` THEN
        ASM_MESON_TAC[]
      ;
        note `i(m+1):int = --i(m)` [] THEN
        int_linear `i(m+1):int = -- i(m) /\ i(m+1) < &0 ==> ~(i(m) < &0)` THEN
        note `{hol_latticescale} < u * divsteps_s zpow (&m + i m)` [] THEN
        num_linear `&(m+1) = &m + &1:int` THEN
        int_linear `&m + i(m):int = (&m + &1) + --(--i(m)) - &1` THEN
        note `{hol_latticescale} < u * divsteps_s zpow ((&m + &1) + --(--i(m)) - &1)` [] THEN
        note `{hol_latticescale} < u * divsteps_s zpow (&(m+1) + --(i(m+1)) - &1)` [] THEN
        ASM_MESON_TAC[]
      ]
    ]
  ]
)'''

def prove_iteration_sizebound_simple():
  # XXX: use latticescale

  return fr'''prove(`
  (!x y. divsteps_H1 x y ==> divsteps_Houter x y) ==>
  (!x y. divsteps_H0 x y ==> divsteps_H1 (((&1) * x + (&0) * y) / divsteps_s pow 1) (((&0) * x + (&1 / &2) * y) / divsteps_s pow 1)) ==>
  (!x y. divsteps_H0 x y ==> divsteps_H1 (((&1) * x + (&0) * y) / divsteps_s pow 1) (((&1 / &2) * x + (&1 / &2) * y) / divsteps_s pow 1)) ==>
  (!x y. divsteps_H1 x y ==> divsteps_H1 (((&0) * x + (&1) * y) / divsteps_s pow 1) (((-- &1 / &2) * x + (&1 / &2) * y) / divsteps_s pow 1)) ==>
  (!x y. divsteps_H1 x y ==> divsteps_H0 (((&0) * x + (&1 / &2) * y) / divsteps_s pow 2) (((-- &1 / &2) * x + (&1 / &4) * y) / divsteps_s pow 2)) ==>
  (!x y. divsteps_H1 x y ==> divsteps_H0 (((&0) * x + (&1 / &4) * y) / divsteps_s pow 4) (((-- &1 / &4) * x + (&1 / &16) * y) / divsteps_s pow 4)) ==>
  (!x y. divsteps_H1 x y ==> divsteps_H0 (((&0) * x + (&1 / &4) * y) / divsteps_s pow 4) (((-- &1 / &4) * x + (&3 / &16) * y) / divsteps_s pow 4)) ==>
  (!x y. divsteps_H1 x y ==> divsteps_H1 (((&33 / &64) * x + (&33 / &512) * y) / divsteps_s pow 2) (((&0) * x + (&33 / &64) * y) / divsteps_s pow 2)) ==>
  (!x y. divsteps_H1 x y ==> divsteps_H1 (((&33 / &64) * x + (-- &33 / &512) * y) / divsteps_s pow 2) (((&0) * x + (&33 / &64) * y) / divsteps_s pow 2)) ==>
  !i:num->int f:num->real g:num->real u:real.
  i(0) = &0 ==>
  (!n. (i(n+1) = &1 + i(n) /\ f(n+1) = f(n) /\ g(n+1) = g(n) / &2)
    \/ (if i(n) < &0 
        then i(n+1) = &1 + i(n) /\ f(n+1) = f(n) /\ g(n+1) = (g(n)+f(n)) / &2
        else i(n+1) = -- i(n) /\ f(n+1) = g(n) /\ g(n+1) = (g(n)-f(n)) / &2)
  ) ==>
  &0 < u ==>
  divsteps_H1 (f(0)/u) (g(0)/u) ==>
  (!n. integer(f(n))) ==>
  (!n. integer(g(n))) ==>
  !m.
    (!n. n <= m ==> ~(g(n) = &0)) ==>
    {hol_latticescale} < u * divsteps_s pow m
  `,
  REPEAT STRIP_TAC THEN
  {divsteps_qs_setup} THEN
  real_linear `&0 < divsteps_s ==> &0 <= divsteps_s` THEN
  real_linear `&0 < divsteps_s ==> ~(divsteps_s = &0)` THEN
  ASSUME_TAC(UNDISCH_ALL(SPEC`m:num`(UNDISCH_ALL(SPECL[`i:num->int`;`f:num->real`;`g:num->real`;`u:real`](UNDISCH_ALL(iteration_sizebound)))))) THEN
  note `{hol_latticescale} < u * (divsteps_s zpow &m) * divsteps_s zpow (if i(m) < &0 then --i(m) - &1 else i(m))` [REAL_ZPOW_ADD] THEN
  note `{hol_latticescale} < u * (divsteps_s pow m) * divsteps_s zpow (if i(m) < &0 then --i(m) - &1 else i(m))` [REAL_ZPOW_POW] THEN
  int_linear `&0 <= (if i(m:num) < &0:int then --i(m) - &1 else i(m))` THEN
  choosevar `a:num` `(if i(m:num) < &0:int then --i(m) - &1 else i(m)) = &a` [INT_OF_NUM_EXISTS] THEN
  note `{hol_latticescale} < u * (divsteps_s pow m) * divsteps_s zpow &a` [] THEN
  note `{hol_latticescale} < u * (divsteps_s pow m) * divsteps_s pow a` [REAL_ZPOW_POW] THEN
  {specialize_qs}({indent(prove_positive_poly(1-y))}) THEN
  real_linear `&0:real < {hol_QQxy_divsteps(1-y)} ==> divsteps_s < &1` THEN
  ASM_CASES_TAC `a = 0` THENL [
    real_linear `u * (divsteps_s pow m) * divsteps_s pow 0 = u * divsteps_s pow m` THEN
    ASM_MESON_TAC[]
  ;
    note `divsteps_s pow a < &1 pow a` [REAL_POW_LT2] THEN
    note `divsteps_s pow a < &1` [REAL_POW_ONE] THEN
    note `&0 < divsteps_s pow a` [REAL_POW_LT] THEN
    real_linear `&0 < {hol_latticescale}` THEN
    ASM_MESON_TAC[real_lt_extra2]
  ]

)'''

def prove_upow_bound():
  K = proveinterval_field(32)
  u = 30902639 / 41749730
  I_u = K(u).rename('u:real')
  I_u_9437 = monomials(I_u,I_u,[(9437,0)])[9437,0]
  I_2 = K(2)
  I_2_4096 = monomials(I_2,I_2,[(4096,0)])[4096,0]
  I_gap = K(1)-I_u_9437*I_2_4096
  proof = I_gap.proof_gt0()
  proof += (
    f'real_linear `&0:real < {I_gap.name} ==> &2 pow 4096 * u pow 9437 <= &1`',
    'real_linear `&0:real <= &2`',
    'note `&0:real <= &2 pow 4096` [REAL_POW_LE]',
    'note `&0:real <= u` []',
    'note `&0:real <= u pow 9437` [REAL_POW_LE]',
    'note `&0:real <= &2 pow 4096 * u pow 9437` [REAL_LE_MUL]',
    'note `(&2 pow 4096 * u pow 9437) pow b <= &1 pow b` [REAL_POW_LE2]',
    'note `(&2 pow 4096 * u pow 9437) pow b <= &1` [REAL_POW_ONE]',
    'note `(&2 pow 4096 pow b) * (u pow 9437 pow b) <= &1` [REAL_POW_MUL]',
    'note `(&2 pow (4096 * b)) * (u pow (9437 * b)) <= &1` [REAL_POW_POW]',
  )
  I_fuzziness = K(fuzziness).rename('fuzziness:real')
  I_fuzziness_4096 = monomials(I_fuzziness,I_fuzziness,[(4096,0)])[4096,0]
  I_gap2 = I_fuzziness_4096-I_u
  proof += I_gap2.proof_gt0()
  proof += (
    f'real_linear `&0:real < {I_gap2.name} ==> u <= fuzziness pow 4096`',
    'note `&0:real <= &2 pow (4096 * b)` [REAL_POW_LE]',
    'note `&0:real <= u pow (9437 * b)` [REAL_POW_LE]',
    'note `&0:real <= (&2 pow (4096 * b)) * (u pow (9437 * b))` [REAL_LE_MUL]',
    'note `((&2 pow (4096 * b)) * (u pow (9437 * b))) * u <= &1 * fuzziness pow 4096` [REAL_LE_MUL2]',
    'real_linear `((&2 pow (4096 * b)) * (u pow (9437 * b))) * u <= &1 * fuzziness pow 4096 ==> (&2 pow (4096 * b)) * (u pow (9437 * b)) * (u pow 1) <= fuzziness pow 4096`',
    'note `(&2 pow (4096 * b)) * (u pow (9437 * b + 1)) <= fuzziness pow 4096` [REAL_POW_ADD]',
    f'real_linear `{hol_QQ(u)} <= &1:real`',
    'note `u <= &1:real` []',
    'note `u pow (4096 * m - 9437 * b - 1) <= (&1:real) pow (4096 * m- 9437 * b - 1)` [REAL_POW_LE2]',
    'note `u pow (4096 * m - 9437 * b - 1) <= &1:real` [REAL_POW_ONE]',
    'note `&0:real <= u pow (4096 * m - 9437 * b - 1)` [REAL_POW_LE]',
    'note `&0:real <= u pow (9437 * b + 1)` [REAL_POW_LE]',
    'note `&0:real <= (&2 pow (4096 * b)) * (u pow (9437 * b + 1))` [REAL_LE_MUL]',
    'note `((&2 pow (4096 * b)) * (u pow (9437 * b + 1))) * (u pow (4096 * m - 9437 * b - 1)) <= (fuzziness pow 4096) * (&1:real)` [REAL_LE_MUL2]',
    'real_linear `((&2 pow (4096 * b)) * (u pow (9437 * b + 1))) * (u pow (4096 * m - 9437 * b - 1)) <= (fuzziness pow 4096) * (&1:real) ==> (&2 pow (4096 * b)) * ((u pow (9437 * b + 1)) * (u pow (4096 * m - 9437 * b - 1))) <= fuzziness pow 4096`',
    'note `(&2 pow (4096 * b)) * (u pow ((9437 * b + 1) + (4096 * m - 9437 * b - 1))) <= fuzziness pow 4096` [REAL_POW_ADD]',
    'num_linear `9437 * b + 1 <= 4096 * m ==> 4096 * m = (9437 * b + 1) + (4096 * m - 9437 * b - 1)`',
    'note `(&2:real pow (4096 * b)) * (u pow (4096 * m)) <= fuzziness pow 4096` []',
    'note `(&2:real pow (b * 4096)) * (u pow (m * 4096)) <= fuzziness pow 4096` [MULT_SYM]',
    'note `(&2:real pow b pow 4096) * (u pow m pow 4096) <= fuzziness pow 4096` [REAL_POW_POW]',
    'note `((&2:real pow b) * (u pow m)) pow 4096 <= fuzziness pow 4096` [REAL_POW_MUL]',
    'num_linear `~(4096 = 0)`',
    f'real_linear `&0:real <= {hol_QQ(fuzziness)}`',
    'note `&0:real <= fuzziness:real` []',
    'note `&2 pow b * u pow m <= fuzziness:real` [REAL_POW_LE2_REV]',
  )
  proof = ' THEN\n  '.join(proof)

  result = fr'''prove(`
  !b:num m:num.
  9437 * b + 1 <= 4096 * m ==>
  &2 pow b * ({hol_QQ(u)}) pow m <= ({hol_QQ(fuzziness)}):real
  `,
  REPEAT STRIP_TAC THEN
  def `u:real` `{hol_QQ(u)}` THEN
  def `fuzziness:real` `{hol_QQ(fuzziness)}` THEN
  {proof} THEN
  note `&2 pow b * u pow m <= ({hol_QQ(fuzziness)}):real` [] THEN
  ASM_MESON_TAC[]
)'''

  return result

def prove_spow_bound():
  if approx:
    return fr'''prove(`
  !b:num m:num.
  9437 * b + 1 <= 4096 * m ==>
  &2 pow b * divsteps_s pow m <= ({hol_QQ(fuzziness)}):real
  `,
  REWRITE_TAC[divsteps_s_definition] THEN
  MESON_TAC[upow_bound]
)'''

  u = 30902639 / 41749730

  return fr'''prove(`
  !b:num m:num.
  9437 * b + 1 <= 4096 * m ==>
  &2 pow b * divsteps_s pow m <= ({hol_QQ(fuzziness)}):real
  `,
  REPEAT STRIP_TAC THEN
  {divsteps_qs_setup} THEN
  {specialize_qs}({indent(prove_positive_poly(u-y))}) THEN
  note `&2 pow b * ({hol_QQ(u)}) pow m <= ({hol_QQ(fuzziness)}):real` [upow_bound] THEN
  real_linear `&0:real < {hol_QQxy_divsteps(u-y)} ==> divsteps_s <= {hol_QQ(u)}` THEN
  real_linear `&0 < divsteps_s ==> &0 <= divsteps_s` THEN
  note `divsteps_s pow m <= ({hol_QQ(u)}) pow m` [REAL_POW_LE2] THEN
  real_linear `&0:real <= &2` THEN
  note `&0:real <= &2 pow b` [REAL_POW_LE] THEN
  note `&2 pow b * divsteps_s pow m <= &2 pow b * ({hol_QQ(u)}) pow m` [REAL_LE_LMUL] THEN
  ASM_MESON_TAC[REAL_LE_TRANS]
)'''

def hol_denouement():
  return fr'''(* ----- denouement *)

let iteration_stability =
{prove_iteration_stability()};;

let iteration_sizebound =
{prove_iteration_sizebound()};;

let iteration_sizebound_simple =
{prove_iteration_sizebound_simple()};;

{savememory}

let upow_bound =
{prove_upow_bound()};;

let spow_bound =
{prove_spow_bound()};;

{savememory}

let endtoend = prove(`
  (!x y. divsteps_hinit_0_1 x y ==> divsteps_H1 (({hol_stretch})*x) (({hol_stretch})*y)) ==>
  (!x y. divsteps_H1 x y ==> divsteps_Houter x y) ==>
  (!x y. divsteps_H0 x y ==> divsteps_H1 (((&1) * x + (&0) * y) / divsteps_s pow 1) (((&0) * x + (&1 / &2) * y) / divsteps_s pow 1)) ==>
  (!x y. divsteps_H0 x y ==> divsteps_H1 (((&1) * x + (&0) * y) / divsteps_s pow 1) (((&1 / &2) * x + (&1 / &2) * y) / divsteps_s pow 1)) ==>
  (!x y. divsteps_H1 x y ==> divsteps_H1 (((&0) * x + (&1) * y) / divsteps_s pow 1) (((-- &1 / &2) * x + (&1 / &2) * y) / divsteps_s pow 1)) ==>
  (!x y. divsteps_H1 x y ==> divsteps_H0 (((&0) * x + (&1 / &2) * y) / divsteps_s pow 2) (((-- &1 / &2) * x + (&1 / &4) * y) / divsteps_s pow 2)) ==>
  (!x y. divsteps_H1 x y ==> divsteps_H0 (((&0) * x + (&1 / &4) * y) / divsteps_s pow 4) (((-- &1 / &4) * x + (&1 / &16) * y) / divsteps_s pow 4)) ==>
  (!x y. divsteps_H1 x y ==> divsteps_H0 (((&0) * x + (&1 / &4) * y) / divsteps_s pow 4) (((-- &1 / &4) * x + (&3 / &16) * y) / divsteps_s pow 4)) ==>
  (!x y. divsteps_H1 x y ==> divsteps_H1 (((&33 / &64) * x + (&33 / &512) * y) / divsteps_s pow 2) (((&0) * x + (&33 / &64) * y) / divsteps_s pow 2)) ==>
  (!x y. divsteps_H1 x y ==> divsteps_H1 (((&33 / &64) * x + (-- &33 / &512) * y) / divsteps_s pow 2) (((&0) * x + (&33 / &64) * y) / divsteps_s pow 2)) ==>
  !i:num->int f:num->real g:num->real M:real m:num.
  i(0) = &0 ==>
  &0 < M ==>
  &0 <= g(0) ==>
  g(0) <= f(0) ==>
  f(0) <= M ==>
  (!n. (i(n+1) = &1 + i(n) /\ f(n+1) = f(n) /\ g(n+1) = g(n) / &2)
    \/ (if i(n) < &0 
        then i(n+1) = &1 + i(n) /\ f(n+1) = f(n) /\ g(n+1) = (g(n)+f(n)) / &2
        else i(n+1) = -- i(n) /\ f(n+1) = g(n) /\ g(n+1) = (g(n)-f(n)) / &2)
  ) ==>
  (!n. integer(f(n))) ==>
  (!n. integer(g(n))) ==>
  M * divsteps_s pow m <= ({hol_fuzziness}) ==>
  ?n. n <= m /\ g(n) = &0
  `,
  REPEAT STRIP_TAC THEN
  note `&0 / M <= g(0) / M` [REAL_LE_DIV2_EQ] THEN
  note `&0 <= g(0) / M` [REAL_ARITH `&0 / M = &0`] THEN
  note `g(0) / M <= f(0) / M` [REAL_LE_DIV2_EQ] THEN
  note `f(0) / M <= M / M` [REAL_LE_DIV2_EQ] THEN
  real_cancel `&0 < M ==> M / M = &1` THEN
  note `f(0) / M <= &1` [] THEN
  real_linear `&0 <= g(0) / M ==> (&0)*(f(0)/M)+(-- &1)*(g(0)/M) <= &0` THEN
  real_linear `f(0) / M <= &1 ==> (&1)*(f(0)/M) + (&0)*(g(0)/M) <= &1` THEN
  real_linear `g(0) / M <= f(0) / M ==> (-- &1)*(f(0)/M) + (&1)*(g(0)/M) <= &0` THEN
  note `divsteps_hinit_0_1 (f(0)/M) (g(0)/M)` [divsteps_hinit_0_1] THEN
  note `divsteps_H1 (({hol_stretch})*(f(0)/M)) (({hol_stretch})*(g(0)/M))` [] THEN
  real_cancel `({hol_stretch})*(f(0)/M) = f(0) / (M * {hol_invstretch})` THEN
  real_cancel `({hol_stretch})*(g(0)/M) = g(0) / (M * {hol_invstretch})` THEN
  note `divsteps_H1 (f(0)/(M * {hol_invstretch})) (g(0)/(M * {hol_invstretch}))` [] THEN
  ASM_CASES_TAC `!n:num. n <= m ==> ~(g(n):real = &0)` THENL [
    real_linear `&0 < M ==> &0 < M * {hol_invstretch}` THEN
    ASSUME_TAC(UNDISCH_ALL(SPEC`m:num`(UNDISCH_ALL(SPECL[`i:num->int`;`f:num->real`;`g:num->real`;`M * {hol_invstretch}`](UNDISCH_ALL(iteration_sizebound_simple)))))) THEN
    real_linear `{hol_latticescale} < (M * {hol_invstretch}) * divsteps_s pow m ==> ~(M * divsteps_s pow m <= ({hol_fuzziness}))` THEN
    ASM_MESON_TAC[]
  ;
    ASM_MESON_TAC[]
  ]
);;

let endtoend_simple = prove(`
  !i:num->int f:num->real g:num->real M:real m:num.
  i(0) = &0 ==>
  &0 < M ==>
  &0 <= g(0) ==>
  g(0) <= f(0) ==>
  f(0) <= M ==>
  (!n. (i(n+1) = &1 + i(n) /\ f(n+1) = f(n) /\ g(n+1) = g(n) / &2)
    \/ (if i(n) < &0 
        then i(n+1) = &1 + i(n) /\ f(n+1) = f(n) /\ g(n+1) = (g(n)+f(n)) / &2
        else i(n+1) = -- i(n) /\ f(n+1) = g(n) /\ g(n+1) = (g(n)-f(n)) / &2)
  ) ==>
  (!n. integer(f(n))) ==>
  (!n. integer(g(n))) ==>
  M * divsteps_s pow m <= {hol_fuzziness} ==>
  ?n. n <= m /\ g(n) = &0
  `,
  REPEAT STRIP_TAC THEN
  note `!x y. divsteps_hinit_0_1 x y ==> divsteps_H1 (({hol_stretch})*x) (({hol_stretch})*y)` [init2stable_simple] THEN
  note `!x y. divsteps_H1 x y ==> divsteps_Houter x y` [theoremouter_simple] THEN
  note `!x y. divsteps_H0 x y ==> divsteps_H1 (((&1) * x + (&0) * y) / divsteps_s pow 1) (((&0) * x + (&1 / &2) * y) / divsteps_s pow 1)` [theorem0] THEN
  note `!x y. divsteps_H0 x y ==> divsteps_H1 (((&1) * x + (&0) * y) / divsteps_s pow 1) (((&1 / &2) * x + (&1 / &2) * y) / divsteps_s pow 1)` [theorem1] THEN
  note `!x y. divsteps_H1 x y ==> divsteps_H1 (((&0) * x + (&1) * y) / divsteps_s pow 1) (((-- &1 / &2) * x + (&1 / &2) * y) / divsteps_s pow 1)` [theorem3] THEN
  note `!x y. divsteps_H1 x y ==> divsteps_H0 (((&0) * x + (&1 / &2) * y) / divsteps_s pow 2) (((-- &1 / &2) * x + (&1 / &4) * y) / divsteps_s pow 2)` [theorem5] THEN
  note `!x y. divsteps_H1 x y ==> divsteps_H0 (((&0) * x + (&1 / &4) * y) / divsteps_s pow 4) (((-- &1 / &4) * x + (&1 / &16) * y) / divsteps_s pow 4)` [theorem_2] THEN
  note `!x y. divsteps_H1 x y ==> divsteps_H0 (((&0) * x + (&1 / &4) * y) / divsteps_s pow 4) (((-- &1 / &4) * x + (&3 / &16) * y) / divsteps_s pow 4)` [theorem_1] THEN
  note `!x y. divsteps_H1 x y ==> divsteps_H1 (((&33 / &64) * x + (&33 / &512) * y) / divsteps_s pow 2) (((&0) * x + (&33 / &64) * y) / divsteps_s pow 2)` [theorem_4scale] THEN
  note `!x y. divsteps_H1 x y ==> divsteps_H1 (((&33 / &64) * x + (-- &33 / &512) * y) / divsteps_s pow 2) (((&0) * x + (&33 / &64) * y) / divsteps_s pow 2)` [theorem_3scale] THEN
  ASSUME_TAC(UNDISCH_ALL(SPECL[`i:num->int`;`f:num->real`;`g:num->real`;`M:real`;`m:num`](UNDISCH_ALL(endtoend)))) THEN
  ASM_MESON_TAC[]
);;

let endtoend_bits_simple = prove(`
  !i:num->int f:num->real g:num->real b:num m:num.
  i(0) = &0 ==>
  &0 <= g(0) ==>
  g(0) <= f(0) ==>
  f(0) <= &2 pow b ==>
  (!n. (i(n+1) = &1 + i(n) /\ f(n+1) = f(n) /\ g(n+1) = g(n) / &2)
    \/ (if i(n) < &0 
        then i(n+1) = &1 + i(n) /\ f(n+1) = f(n) /\ g(n+1) = (g(n)+f(n)) / &2
        else i(n+1) = -- i(n) /\ f(n+1) = g(n) /\ g(n+1) = (g(n)-f(n)) / &2)
  ) ==>
  (!n. integer(f(n))) ==>
  (!n. integer(g(n))) ==>
  9437 * b + 1 <= 4096 * m ==>
  ?n. n <= m /\ g(n) = &0
  `,
  REPEAT STRIP_TAC THEN
  real_linear `&0:real < &2` THEN
  note `&0:real < &2 pow b` [REAL_POW_LT] THEN
  note `&2 pow b * divsteps_s pow m <= ({hol_fuzziness}):real` [spow_bound] THEN
  specialize[`i:num->int`;`f:num->real`;`g:num->real`;`&2:real pow b`;`m:num`]endtoend_simple THEN
  ASM_SIMP_TAC[]
);;

'''

def hol_specialize(bits):
  bits = ZZ(bits)
  if bits < 1: raise ValueError(f'bits={bits} is below 1')
  steps = ceil((9437*bits+1)/4096)

  return fr'''let endtoend_{bits}_simple = prove(`
  !i:num->int f:num->real g:num->real.
  i(0) = &0 ==>
  &0 <= g(0) ==>
  g(0) <= f(0) ==>
  f(0) <= &2 pow {bits} ==>
  (!n. (i(n+1) = &1 + i(n) /\ f(n+1) = f(n) /\ g(n+1) = g(n) / &2)
    \/ (if i(n) < &0 
        then i(n+1) = &1 + i(n) /\ f(n+1) = f(n) /\ g(n+1) = (g(n)+f(n)) / &2
        else i(n+1) = -- i(n) /\ f(n+1) = g(n) /\ g(n+1) = (g(n)-f(n)) / &2)
  ) ==>
  (!n. integer(f(n))) ==>
  (!n. integer(g(n))) ==>
  ?n. n <= {steps} /\ g(n) = &0
  `,
  REPEAT STRIP_TAC THEN
  num_linear `9437 * {bits} + 1 <= 4096 * {steps}` THEN
  specialize[`i:num->int`;`f:num->real`;`g:num->real`;`{bits}`;`{steps}`]endtoend_bits_simple THEN
  ASM_MESON_TAC[]
);;

'''

def timing(note):
  return '["timing","%s",Sys.time()];;\n\n' % note.replace('"',"'").replace('\\',"_")

def prove_everything():
  result0 = timing('start')
  result1 = ''
  result2 = ''
  result0 += hol_topmatter()+timing('topmatter')
  result0 += hol_qsbasics()+timing('qsbasics')
  result2 += hol_initialhulls()+timing('initialhulls')
  result2 += hol_stablehull()+timing('stablehull')
  result2 += hol_init2stable()+timing('init2stable')
  result2 += hol_transitions()+timing('transitions')
  result2 += hol_convexity()+timing('convexity')
  result2 += hol_outer()+timing('outer')
  result2 += hol_latticetheorem()+timing('latticetheorem')
  result2 += hol_denouement()+timing('denouement')
  result2 += hol_specialize(255)+timing('specialize_255')
  result2 += hol_specialize(256)+timing('specialize_256')
  result2 += hol_specialize(512)+timing('specialize_512')
  result2 += hol_specialize(16384)+timing('specialize_16384')
  result1 += hol_proveinterval_lemmas()+timing('proveinterval')
  result1 += hol_positive_lemmas()+timing('positive')
  return result0+result1+result2

print(prove_everything())
