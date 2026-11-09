#!/usr/bin/env python3
"""genbig.py - large KIR programs for timing kopt (the hidden tests include
programs of about 100,000 instructions).

  tools/genbig.py straight 100000 > big1.kir    # one long block
  tools/genbig.py loops 100000 > big2.kir       # thousands of small loops and branches
"""
import random
import sys


def straight(n, rng):
    out = ["func big(v0, v1, v2, v3)", "entry:"]
    live = ["v0", "v1", "v2", "v3"]
    reg = 4
    count = 0
    while count < n - 1:
        r = rng.random()
        d = "v%d" % reg
        reg += 1
        if r < 0.55:
            out.append("  %s %s, %s, %s" % (rng.choice(["add", "sub", "xor", "and", "or", "mul", "shl", "shr"]), d,
                                             rng.choice(live), rng.choice(live + [str(rng.randrange(64))])))
        elif r < 0.7:
            out.append("  and %s, %s, 1023" % (d, rng.choice(live)))
            count += 1
            e = "v%d" % reg
            reg += 1
            out.append("  load %s, %s" % (e, d))
            d = e
        elif r < 0.8:
            out.append("  and %s, %s, 1023" % (d, rng.choice(live)))
            count += 1
            out.append("  store %s, %s" % (d, rng.choice(live)))
        elif r < 0.9:
            out.append("  mac %s, %s, %s, %s" % (d, rng.choice(live), rng.choice(live), rng.choice(live)))
        else:
            out.append("  const %s, %d" % (d, rng.randrange(1000)))
        live.append(d)
        if len(live) > 24:
            live.pop(rng.randrange(len(live) - 4))
        count += 1
    out.append("  ret %s" % live[-1])
    return "\n".join(out) + "\n"


def loops(n, rng):
    out = ["func big(v0, v1)", "entry:", "  const v2, 0", "  jmp b0"]
    count = 3
    b = 0
    while count < n - 10:
        nxt = "b%d" % (b + 1)
        body = rng.randint(2, 8)
        out.append("b%d:" % b)
        out.append("  const v3, 0")
        out.append("  jmp h%d" % b)
        out.append("h%d:" % b)
        out.append("  lt v4, v3, %d" % rng.randint(1, 5))
        out.append("  br v4, l%d, %s" % (b, nxt))
        out.append("l%d:" % b)
        for _ in range(body):
            op = rng.choice(["add", "xor", "mul", "sub"])
            out.append("  %s v2, v2, %s" % (op, rng.choice(["v3", "v0", "v1", "7"])))
        if rng.random() < 0.3:
            out.append("  and v5, v2, 255")
            out.append("  store v5, v3")
        out.append("  add v3, v3, 1")
        out.append("  jmp h%d" % b)
        count += 8 + body
        b += 1
    out.append("b%d:" % b)
    out.append("  ret v2")
    return "\n".join(out) + "\n"


if __name__ == "__main__":
    kind, n = sys.argv[1], int(sys.argv[2])
    rng = random.Random(42)
    sys.stdout.write(straight(n, rng) if kind == "straight" else loops(n, rng))
