"""Generate a 200-plank 'duck on one leg in a tree' plan for the Kapla rule lab.

Coordinates: units of 7.8 mm, plank min corner. Duck parts are written relative to the
leg's centre (cx, cy) and the leg top; the order is chosen greedily so the weight above
the leg stays as close to its centre as possible at every step.
"""
import json, sys
from fractions import Fraction as F

SZ = {'flatX': (15, 3, 1), 'flatY': (3, 15, 1), 'edgeX': (15, 1, 3), 'edgeY': (1, 15, 3),
      'standFacingY': (3, 1, 15), 'standFacingX': (1, 3, 15)}


class P:
    def __init__(s, pose, x, y, z, part):
        s.pose, s.x, s.y, s.z, s.part = pose, F(x), F(y), F(z), part
        dx, dy, dz = SZ[pose]
        s.x1, s.y1, s.z1 = s.x + dx, s.y + dy, s.z + dz

    def c(s):
        return ((s.x + s.x1) / 2, (s.y + s.y1) / 2)


def overlap(a, b):
    return a.x < b.x1 and b.x < a.x1 and a.y < b.y1 and b.y < a.y1 and a.z < b.z1 and b.z < a.z1


def xy(a, b):
    return a.x < b.x1 and b.x < a.x1 and a.y < b.y1 and b.y < a.y1


def build(trunk_levels, body_h, crown_levels, tail_levels, neck_levels):
    plan = []
    # Trunk: square crib tower at (0,0).
    for m in range(2 * trunk_levels):
        L, side = m // 2, (0 if m % 2 == 0 else 12)
        plan.append(P('flatX', 0, side, L, 'trunk') if L % 2 == 0 else P('flatY', side, 0, L, 'trunk'))
    zt = trunk_levels
    # Deck.
    for d in (0, 3, 6, 9, 12):
        plan.append(P('flatX', 0, d, zt, 'canopy'))
    # Crown: pinwheel of leaves sticking out 6 in rotating directions.
    for k in range(crown_levels):
        z = zt + 1 + k
        if k % 2 == 0:
            plan.append(P('flatY', 0, -6, z, 'leaves'))
            plan.append(P('flatY', 12, 6, z, 'leaves'))
        else:
            plan.append(P('flatX', -6, 0, z, 'leaves'))
            plan.append(P('flatX', 6, 12, z, 'leaves'))
    # Leg on deck centre.
    cx, cy = F(15, 2), F(15, 2)
    zl = zt + 1
    plan.append(P('standFacingY', cx - F(3, 2), cy - F(1, 2), zl, 'leg'))
    T = zl + 15

    def fx(xc, yc, z, part):  # flatX centred at (xc, yc) relative to leg centre
        return P('flatX', cx + xc - F(15, 2), cy + yc - F(3, 2), T + z, part)

    def fy(xc, yc, z, part):
        return P('flatY', cx + xc - F(3, 2), cy + yc - F(15, 2), T + z, part)

    zb = 2 + body_h                                  # body top (relative)
    # Crib body: keel, beam, then alternating lane levels (flatX) and tie levels (flatY).
    # Narrow at the bottom so early planks stay balanced on the 3 x 1 leg top.
    body = [fx(0, 0, 0, 'body'), fy(0, 0, 1, 'body'), fx(0, 0, 2, 'body')]
    lanes_at = {4: (0, 3, -3)}
    for h in range(3, 2 + body_h + 1):
        if h % 2 == 1:
            body += [fy(o, 0, h, 'body') for o in (0, 3, -3, 6, -6)]
        else:
            body += [fx(0, o, h, 'body') for o in lanes_at.get(h, (0, 3, -3, 6, -6))]
    zb = 2 + body_h + 1
    rest = []
    # Folded wings: four outer lanes, pushed back 3 (they carry the tail).
    for lane in (0, 3, -3, 6, -6):
        rest.append(fx(-3, lane, zb, 'wings'))
    # Tail: two prongs (lanes +-3), rising backward 1.5 per level.
    for t in range(tail_levels):
        for lane in (3, -3):
            rest.append(fx(F(-9, 2) - F(3, 2) * t, lane, zb + 1 + t, 'tail'))
    # Neck: crossing column centred at x = 3, starting with a flatY at body top.
    xn = F(6)
    for k in range(neck_levels):
        z = zb + k
        rest.append(fy(xn, 0, z, 'neck') if k % 2 == 0 else fx(xn, 0, z, 'neck'))
    zh = zb + neck_levels
    # Head: a small crib on the neck top, placed in a fixed order so it balances on the
    # 3-unit-wide neck plank at every step. The crest sits at the back as a counterweight.
    head = [fx(xn, 0, zh, 'head'),
            fy(xn, 0, zh + 1, 'head'), fy(xn - 3, 0, zh + 1, 'head'), fy(xn + 3, 0, zh + 1, 'head'),
            fx(xn, 3, zh + 2, 'head'), fx(xn, -3, zh + 2, 'head'),
            fx(xn + 3, 0, zh + 2, 'beak'),
            fy(xn - F(3, 2), 0, zh + 3, 'crest'), fy(xn + F(3, 2), 0, zh + 3, 'crest')]
    for p in head:
        p.seq = 'head'
    rest += head
    return plan, body, rest, (cx, cy), zl


def rests_on(p, placed):
    if p.z == 0:
        return True
    return any(q.z1 == p.z and xy(p, q) for q in placed)


def blocked_above(p, placed):
    return any(q.z >= p.z1 and xy(p, q) for q in placed)


def order(plan, body, rest, centre):
    cx, cy = centre
    placed = list(plan)
    above = []  # planks above the leg
    out = list(plan)
    for p in body:
        out.append(p); placed.append(p); above.append(p)
    todo = list(rest)
    while todo:
        best, bs = None, None
        for i, p in enumerate(todo):
            if not rests_on(p, placed) or blocked_above(p, placed):
                continue
            if any(overlap(p, q) for q in placed):
                raise SystemExit(f'overlap: {p.part} {p.pose} {p.x},{p.y},{p.z}')
            # never cover a plank that still has to go in underneath, and keep each
            # part bottom-up
            if any(q is not p and q.z < p.z and (xy(p, q) or q.part == p.part) for q in todo):
                continue
            seq = getattr(p, 'seq', None)
            if seq and next(q for q in todo if getattr(q, 'seq', None) == seq) is not p:
                continue
            pts = above + [p]
            mx = sum(q.c()[0] for q in pts) / len(pts) - cx
            my = sum(q.c()[1] for q in pts) / len(pts) - cy
            score = abs(mx) / F(3, 2) + abs(my) / F(1, 2)
            if bs is None or score < bs:
                best, bs = i, score
        if best is None:
            raise SystemExit('stuck: ' + ', '.join(f'{p.part}@{p.z}' for p in todo))
        p = todo.pop(best)
        out.append(p); placed.append(p); above.append(p)
    return out


def com_report(out, centre, leg_index):
    cx, cy = centre
    worst = (0, 0)
    for k in range(leg_index + 2, len(out) + 1):
        pts = out[leg_index + 1:k]
        mx = sum(q.c()[0] for q in pts) / len(pts) - cx
        my = sum(q.c()[1] for q in pts) / len(pts) - cy
        worst = (max(worst[0], abs(mx)), max(worst[1], abs(my)))
    return worst


if __name__ == '__main__':
    trunk, body_h, crown, tail, neck = 52, 8, 6, 5, 13
    plan, body, rest, centre, zl = build(trunk, body_h, crown, tail, neck)
    out = order(plan, body, rest, centre)
    n = len(out)
    for i, a in enumerate(out):
        for b in out[:i]:
            if overlap(a, b):
                raise SystemExit(f'overlap {i}')
        if not rests_on(a, out[:i]):
            raise SystemExit(f'floating {i} {a.part}')
    leg_index = next(i for i, p in enumerate(out) if p.part == 'leg')
    wx, wy = com_report(out, centre, leg_index)
    parts = {}
    for p in out:
        parts[p.part] = parts.get(p.part, 0) + 1
    top = max(p.z1 for p in out)
    print(f'n={n} parts={parts} top={top} ({float(top) * 7.8 / 10:.1f} cm) '
          f'worst COM offset above leg: x={float(wx):.3f} (limit 1.5), y={float(wy):.3f} (limit 0.5)',
          file=sys.stderr)
    final = out[leg_index + 1:]
    fxm = sum(q.c()[0] for q in final) / len(final) - centre[0]
    print(f'final COM offset x={float(fxm):.3f}', file=sys.stderr)

    def lit(v):
        v = F(v)
        return (str(v.numerator) if v >= 0 else f'({v.numerator})') if v.denominator == 1 else f'({v.numerator}/{v.denominator})'
    ctor = {'flatX': 'fx', 'flatY': 'fy', 'edgeX': 'ex', 'edgeY': 'ey', 'standFacingY': 'sy', 'standFacingX': 'sx'}
    items = [f'{ctor[p.pose]} {lit(p.x)} {lit(p.y)} {lit(p.z)}' for p in out]
    with open(sys.argv[1], 'w') as f:
        f.write('/-- Generated by gen_duck200.py. -/\n')
        f.write('def duck200Steps : Build :=\n  [' + ',\n   '.join(items) + ']\n')
    json.dump([p.part for p in out], open(sys.argv[2], 'w'))
