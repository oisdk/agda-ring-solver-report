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
subst-syntax : ∀ {a b} {A : Set a} (B : A → Set b) {x : A} → B x → ∀ {y} → x ≡ y → B y
subst-syntax B Bx x≈y = subst B x≈y Bx

syntax subst-syntax B Bx x≈y = Bx ∶ B ⟨ x≈y ⟩


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
   node : ∀ {n m} → A → Tree n → Tree m → Tree (n + m + 1)
\end{code}
%</tree>
\begin{code}

 _⇒_ : ∀ {n} → Tree n → ∀ {m} → n ≈ m → Tree m
 x ⇒ n≈m  = subst Tree n≈m x
 open Nat.Reflection

 module M where
  rotˡ : ∀ {n} → Tree n → Tree n
\end{code}
%<*mistake>
\begin{code}
  rotˡ (node {a} x xl (node {b} {c} y yr yl)) = node y (node x xl yl) yr
    ⇒ ∀⟨ a ∷ b ∷ c ∷ [] ⟩
\end{code}
%</mistake>
\begin{code}
  rotˡ tr = tr

 rotˡ : ∀ {n} → Tree n → Tree n
\end{code}
%<*correct>
\begin{code}
 rotˡ (node {a} x xl (node {b} {c} y yl yr)) = node y (node x xl yl) yr
   ⇒ ∀⟨ a ∷ b ∷ c ∷ [] ⟩
\end{code}
%</correct>
\begin{code}
 rotˡ tr = tr

 -- _∪_ : ∀ {n m} → Tree n → Tree m → Tree (n + m)
 -- leaf ∪ ys = ys
 -- node {a} {b} x xl xr ∪ leaf =
 --   node x xl xr ∶ Tree (1 + a + b) + 0
 --   ⟨ solveOver (a ∷ b ∷ []) Nat.ring ⟩
 -- node {a} {b} x xl xr ∪ node {c} {d} y yl yr =
 --   let sz = (1 + a + b) + (1 + c + d)
 --       vs = a ∷ b ∷ c ∷ d ∷ []
 --   in if x ≤ y
 --       then node x (node y yl yr ∪ xr) xl ∶ Tree ⟨ solveOver vs Nat.ring ⟩
 --       else node y (node x xl xr ∪ yr) yl ∶ Tree ⟨ solveOver vs Nat.ring ⟩
\end{code}
