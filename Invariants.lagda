\begin{code}
module Invariants where

open import Data.Bool
open import Data.Nat using (ℕ; suc; zero)
open import Polynomial.Simple.AlmostCommutativeRing
open import Polynomial.Simple.AlmostCommutativeRing.Instances
open import Relation.Binary.PropositionalEquality using (subst; _≡_)
\end{code}
%<*subst-syntax>
\begin{code}
subst-syntax : ∀ {a b} {A : Set a} (B : A → Set b) {x : A} → B x → ∀ y → x ≡ y → B y
subst-syntax B Bx y x≈y = subst B x≈y Bx

syntax subst-syntax B Bx y x≈y = Bx ∶ B · y ⟨ x≈y ⟩
\end{code}
%</subst-syntax>
\begin{code}

open import Polynomial.Simple.Reflection
open import Data.List as List using (List; _∷_; [])

open AlmostCommutativeRing Nat.ring

module UnprovenExample {a} {A : Set a} where
 data Tree : ℕ → Set a where
   leaf : Tree 0
   node : ∀ {b c} → A → Tree b → Tree c → Tree 0
 rotˡ : ∀ {n} → Tree n → Tree n
\end{code}
%<*unproven>
\begin{code}
 rotˡ (node {a} x xl (node {b} {c} y yr yl)) = node y (node x xl yl) yr
\end{code}
%</unproven>
\begin{code}
 rotˡ tr = tr

module Trees {a} {A : Set a} (_≤_ : A → A → Bool) where
\end{code}
%<*tree>
\begin{code}
 data Tree : ℕ → Set a where
   leaf : Tree 0
   node : ∀ {n m} → A → Tree n → Tree m → Tree (1 + n + m)
\end{code}
%</tree>
\begin{code}
 module M where
  rotˡ : ∀ {n} → Tree n → Tree n
\end{code}
%<*mistake>
\begin{code}
  rotˡ (node {a} x xl (node {b} {c} y yr yl)) = node y (node x xl yl) yr
    ∶ Tree · 1 + a + (1 + b + c) ⟨ solveOver (a ∷ b ∷ c ∷ []) Nat.ring ⟩
\end{code}
%</mistake>
\begin{code}
  rotˡ tr = tr

 rotˡ : ∀ {n} → Tree n → Tree n
\end{code}
%<*correct>
\begin{code}
 rotˡ (node {a} x xl (node {b} {c} y yl yr)) = node y (node x xl yl) yr
   ∶ Tree · 1 + a + (1 + b + c) ⟨ solveOver (a ∷ b ∷ c ∷ []) Nat.ring ⟩
\end{code}
%</correct>
\begin{code}
 rotˡ tr = tr

 _∪_ : ∀ {n m} → Tree n → Tree m → Tree (n + m)
 leaf ∪ ys = ys
 node {a} {b} x xl xr ∪ leaf =
   node x xl xr ∶ Tree · (1 + a + b) + 0
   ⟨ solveOver (a ∷ b ∷ []) Nat.ring ⟩
 node {a} {b} x xl xr ∪ node {c} {d} y yl yr =
   let sz = (1 + a + b) + (1 + c + d)
       vs = a ∷ b ∷ c ∷ d ∷ []
   in if x ≤ y
       then node x (node y yl yr ∪ xr) xl ∶ Tree · sz
              ⟨ solveOver vs Nat.ring ⟩
       else node y (node x xl xr ∪ yr) yl ∶ Tree · sz
              ⟨ solveOver vs Nat.ring ⟩
\end{code}
