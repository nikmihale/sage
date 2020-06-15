from __future__ import absolute_import, division

#*****************************************************************************
#  Copyright (C) 2008-2010 John H. Palmieri <palmieri@math.washington.edu>
#  Distributed under the terms of the GNU General Public License (GPL)
#*****************************************************************************

from sage.misc.cachefunc import cached_function


def degrees(n,p=2):
    from sage.rings.all import Integer
    if n <= 0:
        return []

    N = Integer(n // 2 + 1)
    l = [2*(p**i-1) for i in range(1, N.exact_log(p) + 1)] 
    return l

########################################################
# Functions for defining bases.

# These should each return a tuple of tuples of the appropriate form
# for the basis.  For example, at the prime 2, the Milnor basis
# element Sq(a,b,c,...) corresponds to the tuple (a, b, c, ...), while
# at odd primes, the element Q_i Q_j ... P(a, b, ...) corresponds to
# the pair ((i, j, ...), (a, b, ...)).  See each function for more
# information.

def BP_basis(n, p=2, **kwds):
    

    if n == 0:
            return ((),)

    from sage.rings.infinity import Infinity
    from sage.combinat.integer_vector_weighted import WeightedIntegerVectors

    result = []
    for mono in WeightedIntegerVectors(n, degrees(n, p=p)):
        exponents = list(mono)
        while exponents and exponents[-1] == 0:
            exponents.pop(-1)
        result.append(tuple(exponents))
    return tuple(result)
