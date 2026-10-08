# This was made by Ben Leviloff. The techniques follow the paper "Algebres L^1 p-adiques" by Fresnel and De Mathan. I used AI to help with the syntax and implementation, but it did not have access to the original paper. 


# ============================================================
# Settings
# ============================================================

p = 3 #prime of Q_p
prec = 10 #number of digits for precision
N = 2 #constructs f_1, ..., f_N. Large N may be computationally expensive
d = 4 # f_N is convoluted with itself at the end d times
epsilon = 5 # constant that is used in the calculations, if it's too low code won't work.

# Note: There are a number of choices in this code for the values of the sequences s_k, r_k, and lamda_k 
# Feel free to change these choices around, they may improve optimization
# Line 180-186 overrides the creation of lamda_k for N = 2 and provides more optimized values.


# ============================================================
# Roots of unity and F_{s,lambda}
# ============================================================

def make_ambient_field(top_level):

    K = Qp(p, prec=prec)
    R = PolynomialRing(K, 'u')
    u = R.gen()

    eisenstein_poly = R(cyclotomic_polynomial(p^top_level)(u + 1))

    L = K.extension(eisenstein_poly, names='pi')
    pi = L.gen()
    zeta = 1 + pi

    return L, zeta


def B_exponents(s, lam):
    """Return exponents e such that zeta_s^e belongs to B_{s,lam}. """

    if s < 1:
        raise ValueError("s must be positive")

    if lam < 0 or lam > 1:
        raise ValueError("lam must lie in [0,1]")

    q = [ZZ(floor(lam * p^t)) for t in range(s)]
    chosen_exponents = set()

    def choose_in_coset(residue, t, target):
        if t == 0:
            if target == 1:
                chosen_exponents.add(residue % p^s)
            return

        child_minimum = q[t - 1]
        child_capacity = p^(t - 1)

        child_targets = [child_minimum for j in range(p)]
        extra = target - p * child_minimum

        for j in range(p):
            amount = min(extra, child_capacity - child_minimum)
            child_targets[j] += amount
            extra -= amount

        modulus = p^(s - t)

        for j in range(p):
            child_residue = residue + j * modulus

            choose_in_coset(
                child_residue,
                t - 1,
                child_targets[j]
            )

    root_target = q[s - 1]

    for residue in range(1, p):
        choose_in_coset(residue, s - 1, root_target)

    desired_size = ZZ(floor(lam * p^(s - 1) * (p - 1)))

    for exponent in range(1, p^s):
        if len(chosen_exponents) == desired_size:
            break

        if exponent % p != 0 and exponent not in chosen_exponents:
            chosen_exponents.add(exponent)

    return chosen_exponents


def F_in_ambient_field(s, lam, P, zeta_top, top_level,
                       argument=None):
    """
    Construct F_{s,lam}(argument) in the polynomial ring P.
    """

    if s < 1 or s > top_level:
        raise ValueError("Need 1 <= s <= top_level")

    X = P.gen()

    if argument is None:
        argument = X
    else:
        argument = P(argument)

    # A primitive p^s-th root of unity.
    zeta_s = zeta_top^(p^(top_level - s))

    polynomial = P.one()

    for exponent in B_exponents(s, lam):
        alpha = zeta_s^exponent
        polynomial *= (argument - alpha) * (1 - alpha)^(-1)

    return polynomial


def F(s, lam):
    """
    Return F_{s,lam}(X).
    """

    L, zeta = make_ambient_field(s)
    P = PolynomialRing(L, 'X')

    return F_in_ambient_field(s, lam, P, zeta, s)


# ============================================================
# delta, s_0, r_k, lambda_k, and s_k
# ============================================================

def make_sequences(epsilon):
    if epsilon <= 0:
        raise ValueError("epsilon must be positive")

    if N < 2:
        raise ValueError("N must be at least 2")

    epsilon = RR(epsilon)
    delta = log(RR(1) + epsilon) / log(RR(p))

    # Smallest s0 with p^(-s0) < (delta*(p-1))/2.
    bound = delta * ((p - 1) / 2)
    s0 = 1

    while RR(p)^(-s0) >= bound:
        s0 += 1

    # Bounds required for lambda_0 and lambda_1.
    lower = max(
        RR(0),
        RR(1) + RR(p)^(-s0) - bound,
        RR(1) - delta / (2 * s0)
    )
    upper = RR(1)

    if lower >= upper:
        raise ValueError(
            "This epsilon does not permit lambda_0 and lambda_1."
        )
    # Declare value for lamda_0 and lamda_1; these can be changed
    lambda_0 = lower + (upper - lower) / 3
    lambda_1 = lower + 2 * (upper - lower) / 3

    # Declare values for r_k; this can be changed
    r = [None] + [ZZ(k) for k in range(1, N + 1)]

    lambdas = [lambda_0, lambda_1]

    # Declare values for lamda_k; this can be changed
    for k in range(2, N + 2):
        lambda_k = lambda_1 + (1 - lambda_1) * RR(k - 1) / (N+1)
        lambdas.append(lambda_k)
    if N == 2:
        lambdas = [
        QQ(3)/10,   # lambda_0
        QQ(7)/10,   # lambda_1
        QQ(3)/4,    # lambda_2
        QQ(99)/100  # lambda_3, needed to construct s_2
    ]

    return delta, s0, r, lambdas



def make_s_sequence(delta, s0, r, lambdas):
    """
    Return S and [s_1, ..., s_{N-1}].
    """

    lambda_0 = lambdas[0]
    lambda_1 = lambdas[1]

    S = ZZ(ceil(((1 - lambda_0) / (lambda_1 - lambda_0)) * s0))

    s_values = []

    for k in range(1, N+1):
        difference = lambdas[k + 1] - lambdas[k]

        # Ensures:
        #
        # (lambda_{k+1}-lambda_k)*s_k
        # - lambda_{k+1}*r_k - 1/(p-1) >= -delta.
        lower_for_delta = (lambdas[k + 1] * r[k] + 1/(p - 1) - delta) / difference

        candidates = [
            s0 + 1,
            ZZ(ceil(lower_for_delta))
        ]
        if k > 1:
            candidates.append(r[k])

        # This makes the relevant expression tend to infinity. I removed it or else this becomes too computationally expensive.
    
        #growth_target = k
        #lower_for_growth = (lambdas[k + 1] * r[k] + growth_target) / difference
        #candidates.append(ZZ(ceil(lower_for_growth)))

        if k == 1:
            candidates.append(S + 1)
        else:
            candidates.append(s_values[-1] + 1)

        s_values.append(max(candidates))

    return S, s_values


# ============================================================
# P_1, ..., P_N
# ============================================================

def make_P_sequence(s0, r, lambdas, s_values):
    """
    Return [None, P_1, ..., P_N].

    Here s_values = [s_1, ..., s_N].
    """

    s_all = [ZZ(s0)] + [ZZ(value) for value in s_values]
    number_of_Ps = len(s_values)

    # The final field contains Gamma_{s_N}.
    top_level = s_all[-1]

    L, zeta_top = make_ambient_field(top_level)

    P = PolynomialRing(L, 'X')
    X = P.gen()

    n = p^s0
    geometric_factor = (X^n - 1) // (X - 1)

    P1 = P(L(p)^(-s0)) * geometric_factor

    for tau in range(s_all[0] + 1, s_all[1] + 1):
        P1 *= F_in_ambient_field(
            tau,
            lambdas[0],
            P,
            zeta_top,
            top_level
        )

    P_values = [None, P1]

    # Build P_2 through P_N.
    for k in range(1, number_of_Ps):
        next_polynomial = P_values[k]

        for tau in range(s_all[k - 1] + 1, s_all[k] + 1):
            F_level = tau - r[k]

            if F_level < 1:
                raise ValueError(
                    "Need tau - r_k >= 1; equivalently r_k <= s_{k-1}."
                )

            next_polynomial *= F_in_ambient_field(
                F_level,
                lambdas[k],
                P,
                zeta_top,
                top_level,
                X^(p^r[k])
            )

        P_values.append(next_polynomial)

    return P_values


# ============================================================
# f_N and convolution powers
# ============================================================

def make_f_values(P_N, s_N):
    """
    Return f_N(zeta^a), for a = 0, ..., p^s_N - 1.

    The list entry a represents the root of unity zeta^a.
    """

    L = P_N.base_ring()
    zeta = 1 + L.gen()
    group_order = p^s_N

    return [P_N(zeta^a) for a in range(group_order)]


def cyclic_convolution(f, g):
    """
    Return the convolution f * g on Gamma_{s_N}.

    If entry a represents zeta^a, then this computes

      (f * g)(zeta^a)
      = sum_b f(zeta^b) * g(zeta^(a-b)).
    """

    group_order = len(f)
    L = f[0].parent()

    R = PolynomialRing(L, 'T')
    T = R.gen()

    polynomial_f = R.zero()
    polynomial_g = R.zero()

    for a in range(group_order):
        polynomial_f += f[a] * T^a
        polynomial_g += g[a] * T^a

    product = polynomial_f * polynomial_g

    result = [L.zero() for a in range(group_order)]

    for exponent, coefficient in product.dict().items():
        result[exponent % group_order] += coefficient

    return result


def convolution_powers(f, max_power):
    """
    Return [None, f, f^2, ..., f^max_power],
    where powers are convolution powers.
    """

    powers = [None, f]
    current_power = f

    for j in range(2, max_power + 1):
        current_power = cyclic_convolution(current_power, f)
        powers.append(current_power)

    return powers


def print_convolution_summary(powers, s_N, sample_size=8):
    """
    Print normalized p-adic valuations of f_N^j at a few roots.
    """

    group_order = p^s_N
    sample_size = min(sample_size, group_order)

    print("Domain: Gamma_{s_N}, with s_N =", s_N)
    print("Number of roots =", group_order)

    for j in range(1, len(powers)):
        values = powers[j]
        valuations = []

        for a in range(sample_size):
            if values[a] == 0:
                valuations.append(Infinity)
            else:
                valuations.append(values[a].normalized_valuation())

        print("f_N^" + str(j))
        print(
            "  normalized valuations at zeta^0 through zeta^" +
            str(sample_size - 1) + " =",
            valuations
        )


def polynomial_valuation(polynomial):
    """
    Return the minimum normalized p-adic valuation of the nonzero
    coefficients of a polynomial.

    The normalization is v_p(p) = 1.
    """

    if polynomial == 0:
        return Infinity

    return min(
        coefficient.normalized_valuation()
        for coefficient in polynomial.coefficients()
        if coefficient != 0
    )


# ============================================================
# Run the construction
# ============================================================

delta, s0, r, lambdas = make_sequences(epsilon)

S, s_values = make_s_sequence(
    delta,
    s0,
    r,
    lambdas
)

s_N = s_values[-1]

P_values = make_P_sequence(
    s0,
    r,
    lambdas,
    s_values
)

P_N = P_values[N]
P_1 = P_values[1]

print("ramification index =", P_1.base_ring().ramification_index())
print("P_1(1) =", P_1(1))
print("v_p(P_1, 0) =", polynomial_valuation(P_1))

print("Building f_N on Gamma_{s_N}, with s_N =", s_N, flush=True)
f_N = make_f_values(P_N, s_N)

print("Computing convolution powers through d =", d, flush=True)
powers = convolution_powers(f_N, d)

print("Printing convolution summary...", flush=True)

f_N = make_f_values(P_N, s_N)

powers = convolution_powers(f_N, d)

print("delta =", delta)
print("s0 =", s0)
print("S =", S)
print("r =", r)
print("lambdas =", lambdas)
print("s_1, ..., s_{N-1} =", s_values)
print("s_N =", s_N)
print("N = ", N)
print_convolution_summary(powers, s_N)