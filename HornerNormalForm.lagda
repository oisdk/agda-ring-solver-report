%<*opening>
\begin{code}
open import Algebra

module HornerNormalForm
  {c} (coeff : RawRing c) where
\end{code}
%</opening>
\begin{code}
open import Data.Nat as ℕ using (ℕ; suc; zero)

record FromNat {a} (A : Set a) : Set a where
  field fromNat : ℕ → A
open FromNat ⦃ ... ⦄ public

{-# BUILTIN FROMNAT fromNat #-}

instance
  natLit : FromNat ℕ
  natLit = record { fromNat = λ x → x }

open import Data.List
open RawRing coeff
module Dense ⦃ _ : FromNat Carrier ⦄ where
 Poly : Set c
 Poly = List Carrier
\end{code}
%<*impl>
\begin{code}
 _⊞_ : Poly → Poly → Poly
 [] ⊞ ys = ys
 (x ∷ xs) ⊞ [] = x ∷ xs
 (x ∷ xs) ⊞ (y ∷ ys) = x + y ∷ xs ⊞ ys

 _⊠_ : Poly → Poly → Poly
 _⊠_ [] _ = []
 _⊠_ (x ∷ xs) =
   foldr (λ y ys → x * y ∷ map (_* y) xs ⊞ ys) []
\end{code}
%</impl>
\begin{code}
 d : Poly
 d =
\end{code}
%<*dense-example>
\begin{code}
  3 ∷ 0 ∷ 2 ∷ 0 ∷ 0 ∷ 4 ∷ 0 ∷ 2 ∷ []
\end{code}
%</dense-example>
%<*eval>
\begin{code}
 ⟦_⟧ : Poly → Carrier → Carrier
 ⟦ xs ⟧ ρ = foldr (λ y ys → ρ * ys + y) 0# xs
\end{code}
%</eval>
\begin{code}
open import Data.Product

infixr 8 _^_
_^_ : Carrier → ℕ → Carrier
x ^ zero = 1#
x ^ suc i = x * (x ^ i)

module S ⦃ _ : FromNat Carrier ⦄ where
\end{code}
%<*sparse-poly>
\begin{code}
 Poly : Set c
 Poly = List (Carrier × ℕ)
\end{code}
%</sparse-poly>
\begin{code}
 d : Poly
 d =
\end{code}
%<*sparse-example>
\begin{code}
  (3 , 0) ∷ (2 , 1) ∷ (4 , 2) ∷ (2 , 1) ∷ []
\end{code}
%</sparse-example>
\begin{code}
module M ⦃ _ : FromNat Carrier ⦄ where
\end{code}
%<*multi>
\begin{code}
 Poly : ℕ → Set c
 Poly zero = Carrier
 Poly (suc n) = List (Poly n × ℕ)
\end{code}
%</multi>
\begin{code}
 one′ : Poly 3
 one′ =
\end{code}
%<*multi-nest>
\begin{code}
  ((((((6 , 0) ∷ []) , 0) ∷ []) , 0) ∷ [])
\end{code}
%</multi-nest>
