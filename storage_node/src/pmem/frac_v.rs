use builtin::*;
use vstd::pcm::*;
use vstd::prelude::*;
use vstd::modes::*;

// This implements a resource for fractional ownership of a ghost variable.
// The fractions are represented as some number out of a compile-time const
// TOTAL value; you can have any fractions from 1 up to TOTAL, and if you
// have TOTAL, you can update the ghost variable.

verus! {
    // Too bad that `nat` and `int` are forbidden as the type of a const generic parameter
    pub enum Fractional<T, const TOTAL: u64> {
        Value { v: T, n: int },
        Empty,
        Invalid,
    }

    impl<T, const TOTAL: u64> Fractional<T, TOTAL> {
        pub open spec fn new(v: T) -> Self {
            Fractional::Value { v: v, n: TOTAL as int }
        }
    }

    impl<T, const TOTAL: u64> PCM for Fractional<T, TOTAL> {
        open spec fn valid(self) -> bool {
            match self {
                Fractional::Invalid => false,
                Fractional::Empty => true,
                Fractional::Value { v: v, n: n } => 0 < n <= TOTAL,
            }
        }

        open spec fn op(self, other: Self) -> Self {
            match self {
                Fractional::Invalid => Fractional::Invalid,
                Fractional::Empty => other,
                Fractional::Value { v: sv, n: sn } => match other {
                    Fractional::Invalid => Fractional::Invalid,
                    Fractional::Empty => self,
                    Fractional::Value { v: ov, n: on } => {
                        if sv != ov {
                            Fractional::Invalid
                        } else if sn <= 0 || on <= 0 {
                            Fractional::Invalid
                        } else {
                            Fractional::Value { v: sv, n: sn+on }
                        }
                    },
                },
            }
        }

        open spec fn unit() -> Self {
            Fractional::Empty
        }

        proof fn closed_under_incl(a: Self, b: Self) {
        }

        proof fn commutative(a: Self, b: Self) {
        }

        proof fn associative(a: Self, b: Self, c: Self) {
        }

        proof fn op_unit(a: Self) {
        }

        proof fn unit_valid() {
        }
    }

    pub struct FractionalResource<T, const TOTAL: u64> {
        r: Resource<Fractional<T, TOTAL>>,
    }

    impl<T, const TOTAL: u64> FractionalResource<T, TOTAL> {
        pub closed spec fn inv(self) -> bool
        {
            self.r.value() is Value
        }

        pub closed spec fn id(self) -> Loc
        {
            self.r.loc()
        }

        pub closed spec fn val(self) -> T
        {
            self.r.value()->v
        }

        pub closed spec fn frac(self) -> int
        {
            self.r.value()->n
        }

        pub open spec fn valid(self, id: Loc, frac: int) -> bool
        {
            self.inv() && self.id() == id && self.frac() == frac
        }

        pub proof fn default() -> (tracked result: FractionalResource<T, TOTAL>)
        {
            let tracked r = Resource::alloc(Fractional::unit());
            FractionalResource{ r }
        }

        pub proof fn alloc(v: T) -> (tracked result: FractionalResource<T, TOTAL>)
            requires
                TOTAL > 0,
            ensures
                result.inv(),
                result.val() == v,
                result.frac() == TOTAL as int,
        {
            let f = Fractional::<T, TOTAL>::new(v);
            let tracked r = Resource::alloc(f);
            FractionalResource { r }
        }

        pub proof fn agree(tracked self: &FractionalResource<T, TOTAL>, tracked other: &FractionalResource<T, TOTAL>)
            requires
                self.inv(),
                other.inv(),
                self.id() == other.id(),
            ensures
                self.val() == other.val(),
        {
            let tracked joined = self.r.join_shared(&other.r);
            joined.validate()
        }

        pub proof fn split_mut(tracked &mut self, n: int) -> (tracked result: FractionalResource<T, TOTAL>)
            requires
                old(self).inv(),
                0 < n < old(self).frac()
            ensures
                result.id() == self.id() == old(self).id(),
                self.inv(),
                result.inv(),
                self.val() == old(self).val(),
                result.val() == old(self).val(),
                self.frac() + result.frac() == old(self).frac(),
                result.frac() == n,
        {
            let tracked mut r = Resource::alloc(Fractional::unit());
            tracked_swap(&mut self.r, &mut r);
            let tracked (r1, r2) = r.split(Fractional::Value { v: r.value()->v,
                                                               n: r.value()->n - n },
                                           Fractional::Value { v: r.value()->v,
                                                               n: n });
            self.r = r1;
            FractionalResource { r: r2 }
        }

        pub proof fn split(tracked self, n: int) ->
            (tracked result: (FractionalResource<T, TOTAL>, FractionalResource<T, TOTAL>))
            requires
                self.inv(),
                0 < n < self.frac()
            ensures
                result.0.id() == result.1.id() == self.id(),
                result.0.inv(),
                result.1.inv(),
                result.0.val() == self.val(),
                result.1.val() == self.val(),
                result.0.frac() + result.1.frac() == self.frac(),
                result.1.frac() == n,
        {
            let tracked mut s = self;
            let tracked r = s.split_mut(n);
            (s, r)
        }

        pub proof fn combine_mut(tracked &mut self, tracked other: FractionalResource<T, TOTAL>)
            requires
                old(self).inv(),
                other.inv(),
                old(self).id() == other.id(),
            ensures
                self.id() == old(self).id(),
                self.inv(),
                self.val() == old(self).val(),
                self.val() == other.val(),
                self.frac() == old(self).frac() + other.frac(),
        {
            let tracked mut r = Resource::alloc(Fractional::unit());
            tracked_swap(&mut self.r, &mut r);
            r.validate_2(&other.r);
            self.r = r.join(other.r);
        }

        pub proof fn combine(tracked self, tracked other: FractionalResource<T, TOTAL>) -> (tracked result: FractionalResource<T, TOTAL>)
            requires
                self.inv(),
                other.inv(),
                self.id() == other.id(),
            ensures
                result.id() == self.id(),
                result.inv(),
                result.val() == self.val(),
                result.val() == other.val(),
                result.frac() == self.frac() + other.frac(),
        {
            let tracked mut s = self;
            s.combine_mut(other);
            s
        }

        pub proof fn update_mut(tracked &mut self, v: T)
            requires
                old(self).inv(),
                old(self).frac() == TOTAL,
            ensures
                self.id() == old(self).id(),
                self.inv(),
                self.val() == v,
                self.frac() == old(self).frac(),
        {
            let tracked mut r = Resource::alloc(Fractional::unit());
            tracked_swap(&mut self.r, &mut r);
            let f = Fractional::<T, TOTAL>::Value { v: v, n: TOTAL as int };
            self.r = r.update(f);
        }

        pub proof fn update(tracked self, v: T) -> (tracked result: FractionalResource<T, TOTAL>)
            requires
                self.inv(),
                self.frac() == TOTAL,
            ensures
                result.id() == self.id(),
                result.inv(),
                result.val() == v,
                result.frac() == self.frac(),
        {
            let tracked mut s = self;
            s.update_mut(v);
            s
        }
    }
}
