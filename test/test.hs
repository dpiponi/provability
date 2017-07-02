import Provability
import Test.QuickCheck

test_simplify = quickCheck $ \p ->
    valid $ p <-> simplify p

test_dnf = quickCheck $ \p ->
    let q = simplify p
    in valid $ q <-> dnf q

test_canonical = quickCheck $ \p ->
    let q = simplify p
    in valid $ q <-> canonical q

main = do
    test_simplify
    test_dnf
    test_canonical
