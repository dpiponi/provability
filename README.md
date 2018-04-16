# Provability

This is a small library for working with Provability Logic (PL).

A quick summary of Provability Logic: you may be familiar with the idea that Gödel's incompleteness theorems talk about the provability of logical propositions within mathematics. To do this, typically you encode propositions and proofs as integers and the question of whether a proposition P is provable is turned into the question of whether the number encoding P has a certain property. It's a non-trivial task to convert provability into a property of integers, and yet the details are arguably unimportant to the key ideas of Gödel's incompleteness theorems. Provability is an abstraction intended to hide those details. We start with Propositional Calculus and introduce a modality □ which has the interpretation "it is provable that" and whose axioms correspond to things we can prove using Gödel's encoding. So, for example □(□p → p) → □p means "if you can prove that proving p implies p, then you can prove p". (This is in fact an axiom of PL and is known as Löb's theorem.)

Amazingly, there is a sense in which everything you might want to prove about provability in general can be proved in PL. Even more surprisingly, PL itself is complete in the sense that there is a terminating algorithm that can check the validity of any proposition of PL. In fact, this repository contains an implementation.

(Status: This is more or less a "complete" project although I may do more development if I think of something.)

It can:

1. Check a proposition of PL is a theorem
2. Apply Craig's interpolation lemma to interpolate between two propositions
3. Apply the Beth definability theorem to convert an implicit definition into an explicit one
4. Find fixed points

The library is fully functional and comes with Haddock documentation.

Some examples of use:

Check validity of □(□p → p) → □p:

    > valid $ Box (Box p :-> p) :-> Box p
    True

Find interpolant between ¬(p ∧q) → (¬r ∧ q) and (t → p) ∨ (t → ¬r):

    > interp $ (Neg (p :/\ q) :-> (Neg r :/\ q)) :-> ((t :-> p) :\/ (t :-> Neg r))
    Just ("p" \/ Neg "r")

Find explicit form for p in (□(p → q) → p) ∧ (p → □q):

    > beth $ \p -> (Box (p --> q) --> p) /\ (p --> Box q)
    Just (Box "q" \/ Box "q") -- which of course simplifies to Just (Box "q")

Find fixed point for p in p ↔ ¬□p:

    > fixedpoint $ \p -> Neg (Box p)
    Dia T
    
Evaluate the valuation I describe at https://plus.google.com/+DanPiponi/posts/RpwQAD4jTrb on ¬□p ↔ ¬□(¬□⊥)
   
    > value' $ Neg (Box F) <-> Neg (Box (Neg (Box F)))
    -1    

Refs:

* https://plato.stanford.edu/entries/logic-provability/
* https://en.wikipedia.org/wiki/Provability_logic
* The Logic of Provability, George Boolos, Cambridge, 1993
* First Order Logic, Raymond Smullyan, Dover
* http://blog.sigfpe.com/2011/04/generalising-godels-theorem-with.html
* https://plus.google.com/+DanPiponi/posts/RpwQAD4jTrb
