# Provability

This is a small library for working with Provability Logic.

It can:

1. Check a proposition is a theorem
2. Apply Craig's interpolation lemma to interpolate between two propositions
3. Apply the Beth definability theorem to convert an implicit definition into an explicit one
4. Find fixed points

The library is fully functional and comes with Haddock documentation.

Some examples of use:

Check validity of □(𝐱p → p) → □p:

    > valid $ Box (Box p :-> p) :-> Box p
    True

Find interpolant between ¬(p ∧q) → (¬r ∧ q) and (t → p) ∨ (t → ¬r):

    > interp $ (Neg (p :/\ q) :-> (Neg r :/\ q)) :-> ((t :-> p) :\/ (t :-> Neg r))
    Just ("p" \/ Neg "r")

Find explicit form for p in □(p → q) → p) ∧ (p → □q):

    > beth $ \p -> (Box (p --> q) --> p) /\ (p --> Box q)
    Just (Box "q" \/ Box "q") -- which of course simplifies to Just (Box "q")

Find fixed point for p in p ↔ ¬□p:

    > fixedpoint $ \p -> Neg (Box p)
    Dia T
