"""Check eight disjoint root intervals for the published L-gct-261 witness."""

# Each pair records the exponent and the numerator of the coefficient.
DENOMINATOR = 10**12
F = ((46227877, DENOMINATOR), (448900690055, -43365112862), (987294467927, 1397048929))
G = ((0, -1000331817298), (454650486655, -43584165131), (1454650486655, 109442842))

# Endpoints of each interval are integers representing multiples of 1/SCALE.
SCALE = 10**65


def multiply_positive(left, right):
    low = left[0] * right[0] // SCALE
    high = (left[1] * right[1] + SCALE - 1) // SCALE
    return low, high


def positive_power(x, exponent):
    result = (SCALE, SCALE)
    factor = (x, x)
    while exponent:
        if exponent % 2:
            result = multiply_positive(result, factor)
        exponent //= 2
        if exponent:
            factor = multiply_positive(factor, factor)
    return result


def main():
    # Expand DENOMINATOR² (1 + f g); the positive multiplier preserves signs.
    terms = [(0, DENOMINATOR**2)] + [(a+b, c*d) for a, c in F for b, d in G]
    signs = []
    for i in range(9):
        numerator = 19999999999997 + 6*i
        denominator = 20000000000000
        point, remainder = divmod(numerator * SCALE, denominator)
        if remainder:
            raise ArithmeticError("Test point is outside the exact fixed-point grid.")
        lower = upper = 0
        for exponent, coefficient in terms:
            low, high = positive_power(point, exponent)
            lower += min(coefficient * low, coefficient * high)
            upper += max(coefficient * low, coefficient * high)
        if lower > 0:
            signs.append("+")
        elif upper < 0:
            signs.append("-")
        else:
            raise ArithmeticError(f"Sign at test point {i} was inconclusive.")
    if "".join(signs) != "+-+-+-+-+":
        raise ArithmeticError(f"Unexpected sequence of signs: {signs}")
    print("Nine increasing positive points: " + " ".join(signs))
    print("Eight disjoint open intervals each contain a root.")


if __name__ == "__main__":
    main()
