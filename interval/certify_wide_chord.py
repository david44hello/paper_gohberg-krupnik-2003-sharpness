#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
"""Verify the two printed wide-chord witnesses using Arb interval arithmetic.

Version 0.10 — release maintainer — 20261028 07:07 ET.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
Requires python-flint 0.9.0; the fixed rational witnesses are printed in the paper.
"""

import argparse
import json

from flint import arb, ctx, fmpq


def rational(numerator, denominator=1):
    """Construct an Arb enclosure of an exact rational."""
    return arb(fmpq(numerator, denominator))


def obstacle_value(constant, exponent, coefficient, radial_log, angle):
    """Evaluate Gamma_C(y,t) with alpha=1 and beta real."""
    first = 2 * radial_log.cosh() + 2 * angle.cos()
    second = (radial_log.exp() + coefficient**2 * (-radial_log).exp()
              + 2 * coefficient * angle.cos())
    if not (first > 0 and second > 0):
        raise ArithmeticError("A positive power base was not certified.")
    return constant**exponent * first**(exponent / 2) - second**(exponent / 2)


def witness(case, constant_override=None):
    """Return a certified interval for the weighted obstacle sum."""
    if case == "proposition_2_1":
        exponent, coefficient, constant = rational(21, 20), rational(1, 2), rational(353, 100)
        angle_gap, center_log, endpoint_log = rational(51741, 10**6), rational(41, 250), rational(3, 250)
    elif case == "section_4_2":
        exponent, coefficient, constant = rational(8, 7), rational(3, 5), rational(367, 250)
        angle_gap, center_log, endpoint_log = rational(27361, 200000), rational(13, 25), rational(101, 1000)
    else:
        raise ValueError(case)
    if constant_override is not None:
        constant = constant_override
    angle = arb.pi() - angle_gap
    weight = -2 * (exponent * angle / 2).cos()
    if not (constant > 1 and constant > abs(coefficient)
            and angle > arb.pi() / exponent and angle < arb.pi() and weight > 0):
        raise ArithmeticError("Wide-chord hypotheses were not certified.")
    endpoint = obstacle_value(constant, exponent, coefficient, endpoint_log, angle)
    center = obstacle_value(constant, exponent, coefficient, center_log, arb(0))
    return 2 * endpoint + weight * center


def verify_witnesses():
    first = witness("proposition_2_1")
    second = witness("section_4_2")
    if not (first < -rational(196, 100000) and second < 0):
        raise ArithmeticError("At least one printed strict bound was not certified.")
    print(json.dumps({"precision_bits": ctx.prec,
                      "proposition_2_1_S": str(first),
                      "section_4_2_S": str(second),
                      "both_strict_bounds_certified": True}))


def test_controls():
    """Reject the old false rounded bound and a false norm witness."""
    if witness("proposition_2_1") < -rational(197, 100000):
        raise AssertionError("The false old rounded bound was accepted.")
    if witness("proposition_2_1", rational(89, 25)) < 0:
        raise AssertionError("The inflated-constant false witness was accepted.")
    print("Both false-claim controls rejected.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--verify", action="store_true")
    mode.add_argument("--test", action="store_true")
    arguments = parser.parse_args()
    ctx.prec = 160
    if arguments.test:
        test_controls()
    else:
        verify_witnesses()


if __name__ == "__main__":
    main()
