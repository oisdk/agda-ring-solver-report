%<*opening>
\begin{code}
open import Algebra

module HornerNormalForm
  {c} (coeff : RawRing c) where
\end{code}
%</opening>
\begin{code}
module Dense where
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
 ⟦ xs ⟧ ρ = foldr (λ y ys → ρ * ys + y) 0# xs
\end{code}
%</eval>
\begin{code}
open import Data.Product
open import Data.List
open RawRing coeff
open import Data.Nat as ℕ using (ℕ; suc; zero)

infixr 8 _^_
_^_ : Carrier → ℕ → Carrier
x ^ zero = 1#
x ^ suc i = x * (x ^ i)

module S where
\end{code}
%<*sparse-poly>
\begin{code}
 Poly : Set c
 Poly = List (Carrier × ℕ)
\end{code}
%</sparse-poly>
\begin{code}
module M where
\end{code}
%<*multi>
\begin{code}
 Poly : ℕ → Set c
 Poly zero = Carrier
 Poly (suc n) = List (Poly n × ℕ)
\end{code}
%</multi>
