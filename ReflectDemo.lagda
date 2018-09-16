\begin{code}
module ReflectDemo where

open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Nat.Properties
open import Polynomials.Ring.Simple.AlmostCommutativeRing
NatRing : AlmostCommutativeRing _ _
NatRing = fromCommutativeSemiring *-+-commutativeSemiring ℕ._≟_
open AlmostCommutativeRing NatRing
open import Polynomials.Ring.Simple.Reflection
open import Data.List
open import Relation.Nullary
\end{code}
%<*refl-lemma>
\begin{code}
lemma : ∀ x y
      → x + y * 1 + 3 ≈ 2 + 1 + x + y
lemma = solve NatRing
\end{code}
%</refl-lemma>
\begin{code}
open import Reflection
open import Data.Unit
open import Relation.Binary.PropositionalEquality using (_≡_)

return-type : Set
return-type =
\end{code}
%<*return-type>
\begin{code}
  Term → TC ⊤
\end{code}
%</return-type>
%<*occ-of>
\begin{code}
natTerm : ℕ → Term
natTerm zero = con (quote ℕ.zero) []
natTerm (suc i) =
  con
    (quote suc)
    (arg (arg-info visible relevant)
    (natTerm i) ∷ [])

mutual
  occOf : Name → Term → ℕ
  occOf n (var _ args) = occsOf n args
  occOf n (con c args) = occsOf n args
  occOf n (def f args) with n ≟-Name f
  ... | yes p = suc (occsOf n args)
  ... | no ¬p = occsOf n args
  occOf n (lam v (abs s x)) = occOf n x
  occOf n (pat-lam cs args) = occsOf n args
  occOf n (pi a (abs s x)) = occOf n x
  occOf n _ = 0

  occsOf : Name → List (Arg Term) → ℕ
  occsOf n [] = 0
  occsOf n (arg i x ∷ xs) =
    occOf n x + occsOf n xs

macro
  occurencesOf : Name
               → Term
               → Term
               → TC ⊤
  occurencesOf nm xs hole =
    unify hole (natTerm (occOf nm xs))

occPlus :
  occurencesOf _+_ (λ x y → 2 + 1 + x + y)
  ≡ 3
occPlus = refl
\end{code}
%</occ-of>
