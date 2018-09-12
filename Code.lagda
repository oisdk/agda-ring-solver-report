\begin{code}
module Code where
open import Function
import Algebra
module MonDef where
  open import Level
  open import Relation.Binary
  open import Algebra.FunctionProperties
  open import Algebra.Structures
\end{code}
%<*mon-def>
\begin{code}
  record Monoid c ℓ : Set (suc (c ⊔ ℓ)) where
    infixl 7 _∙_
    infix  4 _≈_
    field
      Carrier   : Set c
      _≈_       : Rel Carrier ℓ
      _∙_       : Op₂ Carrier
      ε         : Carrier
      isMonoid  : IsMonoid _≈_ _∙_ ε
\end{code}
%</mon-def>
\begin{code}
module MonIdent {c ℓ}
                (M : Algebra.Monoid c ℓ) where
  open Algebra.Monoid M
  open import Relation.Binary.EqReasoning setoid
  open import Data.Nat
  open import Data.Fin
  open import Data.Vec as Vec using (Vec; lookup)
\end{code}
%<*mon-ident>
\begin{code}
  ident  : ∀ w x y z
         →  w ∙ (((x ∙ ε) ∙ y) ∙ z)
         ≈ (w ∙ x) ∙ (y ∙ z)
\end{code}
%</mon-ident>
%<*mon-proof>
\begin{code}
  ident w x y z =
    begin
      w ∙ (((x ∙ ε) ∙ y) ∙ z)
    ≈⟨ refl ⟨ ∙-cong ⟩ assoc (x ∙ ε) y z ⟩
      w ∙ ((x ∙ ε) ∙ (y ∙ z))
    ≈⟨ sym (assoc w (x ∙ ε) (y ∙ z)) ⟩
      (w ∙ (x ∙ ε)) ∙ (y ∙ z)
    ≈⟨ (refl ⟨ ∙-cong ⟩ identityʳ x) ⟨ ∙-cong ⟩ refl ⟩
      (w ∙ x) ∙ (y ∙ z)
    ∎
\end{code}
%</mon-proof>
%<*list-def>
\begin{code}
  infixr 5 _∷_
  data List (i : ℕ) : Set where
    [] : List i
    _∷_ : Fin i → List i → List i
\end{code}
%</list-def>

%<*list-monoid>
\begin{code}
  infixr 5 _⊙_
  _⊙_ : ∀ {i} → List i → List i → List i
  [] ⊙ ys = ys
  (x ∷ xs) ⊙ ys = x ∷ xs ⊙ ys
\end{code}
%</list-monoid>
\begin{code}
\end{code}
%<*list-trans>
\begin{code}
  _μ : ∀ {i} → List i → Vec Carrier i → Carrier
  ([] μ) ρ = ε
  ((x ∷ xs) μ) ρ = lookup x ρ ∙ (xs μ) ρ

  infix 9 η_
  η_ : ∀ {i} → Fin i → List i
  η x = x ∷ []
\end{code}
%</list-trans>
\begin{code}
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
\end{code}
%<*list-obvious>
\begin{code}
  obvious
    : (List 4 ∋
    η # 0 ⊙ (((η # 1 ⊙ []) ⊙ η # 2) ⊙ η # 3))
    ≡ (η # 0 ⊙ η # 1) ⊙ (η # 2 ⊙ η # 3)
  obvious = ≡.refl
\end{code}
%</list-obvious>
\begin{code}
  module Exprs where
\end{code}
%<*mon-ast>
\begin{code}
    data Expr (i : ℕ) : Set c where
      _⊕_  : Expr i → Expr i → Expr i
      e    : Expr i
      ν    : Fin i → Expr i
\end{code}
%</mon-ast>
%<*eval-ast>
\begin{code}
    ⟦_⟧ : ∀ {i} → Expr i → Vec Carrier i → Carrier
    ⟦ x ⊕ y ⟧ ρ  = ⟦ x ⟧ ρ ∙ ⟦ y ⟧ ρ
    ⟦ e ⟧ ρ      = ε
    ⟦ ν i ⟧ ρ    = lookup i ρ
\end{code}
%</eval-ast>
\begin{code}
  open import Algebra.Solver.Monoid M renaming (id to e)
\end{code}
%<*ident-auto-proof>
\begin{code}
  ident′  : ∀ w x y z
          →  w ∙ (((x ∙ ε) ∙ y) ∙ z)
          ≈ (w ∙ x) ∙ (y ∙ z)
  ident′ = solve 4
    (  λ w x y z
       → w ⊕ (((x ⊕ e) ⊕ y) ⊕ z)
       ⊜ (w ⊕ x) ⊕ (y ⊕ z))
    refl
\end{code}
%</ident-auto-proof>
%<*ident-infer-proof>
\begin{code}
  ident-infer : ∀ w x y z →  _
  ident-infer = solve 4
    (  λ w x y z
       → w ⊕ (((x ⊕ e) ⊕ y) ⊕ z)
       ⊜ (w ⊕ x) ⊕ (y ⊕ z))
    refl
\end{code}
%</ident-infer-proof>
