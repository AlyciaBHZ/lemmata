"""Reproduce the exact integer separation; no floating-point arithmetic."""

a = [1, -1, 1, -1, -1, 1, -1, 1, -1, 1, -1, 1, -1, -1, 1, -1, 1]
b = [-1, 1, -1, 1, -1, 1, -1, 1, 1, -1, 1, -1, 1, -1, 1, 1, -1]
c = [1, -1, 1, 1, -1, 1, -1, 1, -1, 1, -1, -1, 1, -1, 1, -1, 1]
w = [-15, 27, -21, 8, 59, 24, -5, -6, 10]


def coordinates(a, b, c):
    coeff = [0] * 17
    for i in range(17):
        for j in range(17):
            for k in range(17):
                t = i + j + k
                coeff[t % 17] += (-1) ** (t // 17) * a[i] * b[j] * c[k]
    assert all((coeff[r] - coeff[17 - r]) % 2 == 0 for r in range(1, 9))
    return [coeff[0]] + [(coeff[r] - coeff[17 - r]) // 2 for r in range(1, 9)]


def frequency(h):
    return [(-1) ** (h * i // 17) * (1 if h * i % 17 < 9 else -1)
            for i in range(17)]


def dot(x, y):
    return sum(s * t for s, t in zip(x, y))


V = [coordinates(frequency(h), frequency(h), frequency(h))
     for h in range(1, 18, 2)]
Q = coordinates(a, b, c)
assert Q == [-141, 133, -109, 69, -13, -43, 91, -123, 139]
assert [dot(w, v) for v in V] == [
    8295, -8385, -8313, 8383, 8271, -8345, -8169, -8417, -7225
]
assert len({tuple(v) for v in V} | {tuple(-s for s in v) for v in V}) == 18
assert dot(w, Q) == 8421 > max(abs(dot(w, v)) for v in V) == 8417
print("Exact certificate: 18 distinct signed frequency points; 8421 > 8417")
