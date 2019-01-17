\begin{code}
module SetoidApplications where

open import Level
open import Relation.Binary
\end{code}


%<*traced>
\begin{code}
module Trace {a b}
             {A : Set a}
             (_R_ : A → A → Set b)
             (sym′ : Symmetric _R_) where

  data _⋯_ (x : A) : A → Set (a ⊔ b) where
    [] : x ⋯ x
    _∷_ : ∀ {y z}
        → x R y
        → y ⋯ z
        → x ⋯ z

  refl : Reflexive _⋯_
  refl = []

  trans : Transitive _⋯_
  trans [] ys = ys
  trans (x ∷ xs) ys = x ∷ trans xs ys

  sym : Symmetric _⋯_
  sym = go []
    where
    go : ∀ {x y z} → y ⋯ z → y ⋯ x → x ⋯ z
    go xs [] = xs
    go xs (y ∷ ys) = go (sym′ y ∷ xs) ys
\end{code}
%</traced>
