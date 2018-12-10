%<*opening>
\begin{code}
open import Algebra

module HornerNormalForm
  {c} (coeff : RawRing c) where
\end{code}
%</opening>
\begin{code}
open import Data.List
open RawRing coeff
\end{code}
%<*impl>
\begin{code}
Poly : Set c
Poly = List Carrier

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
%<*eval>
\begin{code}
⟦_⟧ : Poly → Carrier → Carrier
⟦ x ⟧ ρ = foldr (λ y ys → y + ρ * ys) 0# x
\end{code}
%</eval>
