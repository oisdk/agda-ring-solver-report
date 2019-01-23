\begin{code}
module PerformanceOfTypeChecking where

open import Data.Nat hiding (_^_)
open import Relation.Binary.PropositionalEquality
open import Data.Product

Carrier : Set
Carrier = ℕ
\end{code}
%<*pow-ident>
\begin{code}
_^_+1 : Carrier → ℕ → Carrier
ρ ^ zero  +1  = ρ
ρ ^ suc i +1  = (ρ ^ i +1) * ρ

_*⟨_⟩^_ : Carrier → Carrier → ℕ → Carrier
ρ *⟨ xs ⟩^ zero  = xs
ρ *⟨ xs ⟩^ suc i = (ρ ^ i +1) * xs

_^_ : Carrier → ℕ → Carrier
x ^ zero = 1
x ^ suc i = x ^ i +1
\end{code}
%</pow-ident>
%<*dense-term-small>
\begin{code}
obligation : ∀ x →
  x * (x * (x * 0 + 1) + 0) + 2 ≡
  x * (x * (x * 0 + 1) + 0) + 2
obligation _ = refl
\end{code}
%</dense-term-small>
\begin{code}
postulate
 dense-term : ∀ x →
  x * (x * (x * (x * (x * (x * (x * (x * 0 + 2) + 0) + 4) + 0) + 0) + 2) + 0) + 3 ≡
\end{code}
%<*dense-term>
\begin{code}
  x *
      (x *
           (x *
                (x *
                     (x *
                          (x *
                               (x *
                                    (x *
                                         0
                                    + 2)
                               + 0)
                          + 4)
                     + 0)
                + 0)
           + 2)
      + 0)
  + 3
\end{code}
%</dense-term>
\begin{code}
sparse-term : ∀ x →
  x ^ 0 * (x * (x ^ 1 * (x * (x ^ 2 * (x * (x ^ 1 * (x * 0 + 2)) + 4)) + 2)) + 3) ≡
\end{code}
%<*sparse-term>
\begin{code}
 x ^ 0 * (x *
  (x ^ 1 * (x *
    (x ^ 2 * (x *
      (x ^ 1 * (x *
        0
       + 2))
     + 4))
   + 2))
 + 3)
\end{code}
%</sparse-term>
\begin{code}
sparse-term _ = refl
module Rev where
  open import Data.List as List using (List; _∷_; []; foldr)
  Poly : Set
  Poly = List Carrier
\end{code}
%<*backwards-eval>
\begin{code}
  ⟦_⟧ : Poly → Carrier → Carrier
  ⟦ xs ⟧ ρ = foldr (λ y ys → y + ys * ρ) 0 xs
\end{code}
%</backwards-eval>
%<*reduction>
\begin{code}
progress : ∀ x →
  2 + (0 + (1 + 0 * x) * x) * x ≡
  suc (suc ((x + 0) * x))
progress _ = refl
\end{code}
%</reduction>
%<*kleene>
\begin{code}
mutual
  data _⋆ {a} (A : Set a) : Set a where
    [] : A ⋆
    [_] : A ⁺ → A ⋆

  infixr 3 _&_
  record _⁺ {a} (A : Set a) : Set a where
    inductive
    constructor _&_
    field
      head : A
      tail : A ⋆
\end{code}
%</kleene>
%<*no-ident>
\begin{code}
Poly : Set
Poly = (Carrier × ℕ) ⋆

⟦_⟧ : Poly → Carrier → Carrier
⟦ [] ⟧ _ = 0
⟦ [ xs ] ⟧ = ⟦ xs ⟧⁺
  where
  ⟦_⟧⁺ : (Carrier × ℕ) ⁺ → Carrier → Carrier
  ⟦ x , i & [] ⟧⁺ ρ = ρ *⟨ x ⟩^ i
  ⟦ x , i & [ xs ] ⟧⁺ ρ =
    ρ *⟨ ρ * ⟦ xs ⟧⁺ ρ + x ⟩^ i

infixr 3 _∷_
pattern _∷_ x xs = [ x & xs ]
\end{code}
%</no-ident>
\begin{code}
small′ : ∀ x →
  ⟦ 3 , 0 ∷ 2 , 1 ∷ 4 , 2 ∷ 2 , 1 ∷ [] ⟧ x ≡
\end{code}
%<*small-eval>
\begin{code}
 x *⟨ x *
   (x *⟨ x *
     (x *⟨ x *
       (x *⟨ 2 ⟩^ 1)
     + 4 ⟩^ 2)
   + 2 ⟩^ 1)
 + 3 ⟩^ 0
\end{code}
%</small-eval>
\begin{code}
small′ _ = refl
\end{code}
\begin{code}
small :
\end{code}
%<*small-force>
\begin{code}
 ∀ x →
 ⟦ 3 , 0 ∷ 2 , 1 ∷ 4 , 2 ∷ 2 , 1 ∷ [] ⟧ x
                 ≡
           x *
             (x * (x *
               ((x * x) * (x *
                 (x * 2)
               + 4))
             + 2))
           + 3
\end{code}
%</small-force>
\begin{code}
small _ = refl
\end{code}

x * (x * (x * ((x * x) * (x * (x * 2) + 4)) + 2)) + 3
