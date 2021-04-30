from sage.all import *
from sage.combinat.free_module import CombinatorialFreeModule


class GenericBrownPetersonAlgebra(CombinatorialFreeModule):
    @staticmethod
    def __classcall__(self, p=2, n=2):
        return super(GenericBrownPetersonAlgebra, self).__classcall__(self, p=p, n=n)

    def __init__(self, p=2, n=2):
        """
        
        n : the grading
        """
        from sage.arith.all import is_prime
        from sage.sets.set_from_iterator import EnumeratedSetFromIterator
        from sage.categories.infinite_enumerated_sets import InfiniteEnumeratedSets
        from sage.categories.graded_hopf_algebras_with_basis import GradedHopfAlgebrasWithBasis
        from functools import partial
        from .brown_peterson_bases import BP_basis
        if not is_prime(p):
            raise ValueError("%s is not prime." % p)
        self._prime = p
        # This would allow infinite rings with weights (lambda is to be taken from input)
        # degrees=itertools.chain((lambda x: 2*(p**x - 1))(t) for t in IntegerRange(Integer(0),Infinity))
        # R=PolynomialRing(ZZ,n,names='m',order=TermOrder('wdeglex',[t for (i,t) in zip(range(n),degrees)]))
        # for h in R.gens():print(h,h.degree())
        _variables = ['m_%s' % k for k in range(1, n+1)]
        _T = TermOrder("wdeglex", [2 * (self._prime ** t - 1) for t in range(1, n+1)])
        base_ring = PolynomialRing(Zp(self._prime, prec=5), _variables, order=_T, implementation='generic')
        basis_category = InfiniteEnumeratedSets()
        basis_set = EnumeratedSetFromIterator(self.basis_key_iterator,
                                              category=basis_category,
                                              name="basis key family of %s" % self,
                                              cache=False)
        self._basis_func = partial(BP_basis, p=p)
        cat = GradedHopfAlgebrasWithBasis(base_ring)
        CombinatorialFreeModule.__init__(self, base_ring, basis_set, element_class=self.Element, category=cat, scalar_mult=' ')


    def basis_key_iterator(self):
        from .brown_peterson_bases import BP_basis
        from sage.sets.integer_range import IntegerRange
        from sage.rings.integer import Integer
        from sage.rings.infinity import Infinity
        from functools import partial
        import itertools

        # HMMMMMMMM
        if self.is_finite():
            maxdim = self.top_class().degree()
            Ir = IntegerRange(Integer(0), Integer(maxdim + 1))
        else:
            Ir = IntegerRange(Integer(0), Infinity)
        pfunc = partial(BP_basis, p=self.prime())
        return itertools.chain.from_iterable(pfunc(dim) for dim in Ir)

    def prime(self):
        return self._prime
        # self.base_ring().base_ring().prime() ?

    def _repr_(self):
        return "Brown-Peterson algebra over %s" % self.base_ring()

    def _latex_(self):
        # TODO
        return None

    def _repr_term(self, t):
        #it prints in homogen component ed by ((1+O(2^20)) r(0,1), (1+O(2^20)) r(3)) ove
        # and >>> r(1) outputs         [1] 1
        #  TODO fix 
        from .brown_peterson_misc import monomial_to_string
        return monomial_to_string(t)

    def _latex_term(self, t):
        import re
        s = self._repr_term(t)
        s = re.sub(r"([(][0-9,]*[)])",r"_{\1}", s)
        s = s.replace("r", "\\text{r}")
        return s

    def homogeneous_component(self, n):
        basis = self._basis_func(n)
        M = CombinatorialFreeModule(self.base_ring(),
            basis,element_class=self.Element)
        M._name = "Vector space spanned by %s" % (tuple(self.monomial(a) for a in basis),)
        return M
    __getitem__ = homogeneous_component

    def one_basis(self):
        return ()

    def product_on_basis(self, left, right):

        # TODO:fix 
        # dies when not enough generators in base ring
        # first check if this ring needs to be expanded
        # then expand ring
        # transfer elements into new algebra with extended ring
        # only then multiply elements
        product_degree = self.degree_on_basis(left, self.prime()) + self.degree_on_basis(right, self.prime())

        if len(self.base_ring().gens()) < 1 + Integer(product_degree // 2).exact_log(self.prime()): # boy what
            A = GenericBrownPetersonAlgebra(p=self.prime(), n=(1 + Integer(product_degree // 2).exact_log(self.prime())))
            return A.product_on_basis(left,right)

        from .brown_peterson_mult import multiplication
        result =  multiplication(left, right, self.base_ring())
        return self._from_dict(result)

    # def coproduct_on_basis(self, t):
    #     # TODO
    #     return None
    # def coproduct(self, t):
    #     # TODO
    #     return None

    # def antipode_on_basis(self, t):
    #     # TODO
    #     return None
    # def counit_on_basis(self, t):
    #     # TODO
    #     return None

    def degree_on_basis(self, t, prime):
        deg = 0
        i = 0
        for k in t:
            i += 1
            deg += 2 * k * (prime**i - 1)
        return deg

    def _coerce_map_from_(self, S):
        from sage.rings.infinity import Infinity
        if self.base_ring().has_coerce_map_from(S):
            return True
        if (isinstance(S, GenericBrownPetersonAlgebra) and self.prime() == S.prime()):
            return self.base_ring().has_coerce_map_from(S.base_ring())
        if (isinstance(S, CombinatorialFreeModule) and S.dimension() < Infinity):
            return self.base_ring().has_coerce_map_from(S.base_ring())
        return False

    def _element_constructor_(self, x):
        if x in self.base_ring():
            return self.from_base_ring_from_one_basis(x)
        if isinstance(x, dict):
            n = self.degree_on_basis(x, self.prime())
            A = BrownPetersonAlgebra(p=self.prime(), n=n)
            x = A._from_dict(x, coerce=True)
        if x in self:
            if x.parent() is self:
                return x
            return self._from_dict(x.monomial_coefficients(), coerce=True)
        raise ValueError("Element does not lie in this Brown-Peterson algebra")

    def __contains__(self, x):
        if x in self.base_ring():
            return True
        if (isinstance(x, self.Element) and x.prime() == self.prime()):
            return True
        return False


    def basis(self, d=None):
        from sage.sets.family import Family
        if d is None:
            return Family(self._indices, self.monomial)
        else:
            return Family([self.monomial(tuple(a)) for a in self._basis_func(d)])


#alter ring:
# sage: B=PolynomialRing(A.base_ring(),['%s'%k for k in A.gens()]+['a%s'%len(A.gen
# ....: s())],len(A.gens())+1,order=TermOrder('wdeglex',(1,2,3)))


    # def update_n(self,n):
        # self.__init__(p=self.prime(), ring_variable=self._ring_variable, n=n)


    def r(self, *nums):
        while nums and nums[-1] == 0:
            nums = nums[:-1]
        if len(nums) == 0 or (len(nums) == 1 and nums[0] == 0):
            return self.one()
        for i in nums:
            try:
                assert Integer(i) >= 0
            except (TypeError, AssertionError):
                raise TypeError("entries must be non-negative integers")
        R = GenericBrownPetersonAlgebra(p=self.prime())
        a = R.monomial(nums)
        return self(a)

    def gens(self):
        from sage.sets.family import Family
        from sage.sets.non_negative_integers import NonNegativeIntegers
        return Family(NonNegativeIntegers(), self.gen)

    def gen(self, i=0):
        # TODO: check if they ddo exist
        return None

    class Element(CombinatorialFreeModule.Element):
        def prime(self):
            return self.base_ring().base_ring().prime()

        def is_homogeneous(self):
            monos = self.support()
            if len(monos) <= 1:
                return True
            from functools import partial
            degree = None
            deg = partial(self.parent().degree_on_basis, prime=self.parent().prime())
            for mono in monos:
                if degree is None:
                    degree = deg(mono)
                elif deg(mono) != degree:
                    return False
            return True

        def degree(self):
            if len(self.support()) == 0:
                raise ValueError("The zero element does not have a well-defined degree.")
            if not self.is_homogeneous():
                raise ValueError("Element is not homogeneous")
            return self.parent().degree_on_basis(self.leading_support(),prime=self.parent().prime())

        def coproduct():
            # TODO
            return None
        def excess(self):
            # TODO: check if exists
            return None

        def is_unit(self):
            return self.parent().one() in self.monimials()

        def is_nilpotent(self):
            # I dont know
            return None



def BrownPetersonAlgebra(p=2, **kwds):
    return GenericBrownPetersonAlgebra(p=p, **kwds)

# def r(*nums):
#     return BrownPetersonAlgebra(p=2).r(*nums)
