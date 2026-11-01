#!/usr/bin/env python3
"""Turn lab results into blueprints for the team viewer (web/README.md, "Blueprint format").

    python3 lab/to_blueprint.py lab/results/lab-results.json lab/results/duck200-parts.json lab/blueprints
    lake exe kapla view lab/blueprints/duck200.json --out out/duck200

One blueprint per design. Each step is one plank. The step card shows the part (for the
200-plank duck) and what the checker says about the build after that step.
"""
import json
import os
import sys
from fractions import Fraction

# Lab pose -> viewer block. The viewer sizes a block along its own axes:
# flat 15 x 3 x 1, edge 15 x 1 x 3, upright 3 x 1 x 15; rot (c, s) turns it about z.
# A quarter turn (c, s) = (0, 1) swaps the x and y sizes.
POSES = {
    'flatX': ('flat', 0, (15, 3, 1)),
    'flatY': ('flat', 1, (3, 15, 1)),
    'edgeX': ('edge', 0, (15, 1, 3)),
    'edgeY': ('edge', 1, (1, 15, 3)),
    'standFacingY': ('upright', 0, (3, 1, 15)),
    'standFacingX': ('upright', 1, (1, 3, 15)),
}


def num(v):
    """An exact fraction as the viewer wants it: an integer, or a string like "15/2"."""
    f = Fraction(v).limit_denominator(1000)
    return int(f) if f.denominator == 1 else f'{f.numerator}/{f.denominator}'


def block(step):
    up, quarter, (dx, dy, dz) = POSES[step['pose']]
    center = [step['x'] + dx / 2, step['y'] + dy / 2, step['z'] + dz / 2]
    return {'up': up, 'rot': {'c': 1 - quarter, 's': quarter}, 'center': [num(c) for c in center]}


def status(step):
    if step['exact'] != 'stable':
        return 'falls'
    if step['solid2mm']:
        return 'solid at 2 mm'
    if step['solid1mm']:
        return 'risky at 2 mm, solid at 1 mm'
    return 'risky at 1 mm'


def blueprint(d, parts):
    f = d['final']
    notes = [
        d['note'],
        f"Height {d['heightMm'] / 10:.1f} cm. Stands at exact positions after "
        f"{d['stableSteps']} of {d['n']} steps; solid at 2 mm after {d['solidSteps']}.",
        f"Finished build: {f['v2mm']} at 2 mm, {f['v_0_25u']} at 1.95 mm, {f['v1mm']} at 1 mm.",
        'Whole plan passes at 2 mm.' if d['checkPlan2mm'] else
        f"Whole plan fails at 2 mm: first at step {d['firstBad']['step'] + 1} ({d['firstBad']['reason']}).",
    ]
    steps = []
    for i, s in enumerate(d['steps']):
        label = f'{parts[i]}: ' if parts else ''
        steps.append({'blocks': [block(s)], 'phase': label + status(s),
                      'approach': 'fromAbove' if s['reach'] == 'above' else (s['reach'] or 'hard to reach')})
    return {'title': d['request'], 'subtitle': f"{d['n']} planks ({d['category']})",
            'notes': notes, 'plan': {'steps': steps}}


def main():
    results, parts_path, out = sys.argv[1:4]
    designs = json.load(open(results))
    duck_parts = json.load(open(parts_path))
    os.makedirs(out, exist_ok=True)
    for d in designs:
        parts = duck_parts if d['id'] == 'duck200' else None
        with open(os.path.join(out, d['id'] + '.json'), 'w') as fh:
            json.dump(blueprint(d, parts), fh, indent=1)
            fh.write('\n')
    print(f'{len(designs)} blueprints in {out}')


if __name__ == '__main__':
    main()
