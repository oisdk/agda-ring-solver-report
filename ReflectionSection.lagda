\begin{code}
module ReflectionSection where
open import Data.Nat as ℕ using (ℕ; suc; zero)
module ExamplePartial where
 open import Polynomial.Simple.AlmostCommutativeRing
 open import Polynomial.Simple.AlmostCommutativeRing.Instances
 open import Polynomial.Simple.Reflection
 open AlmostCommutativeRing Nat.ring
 open import Data.List using (_∷_; [])
 open import Function
 open import Relation.Binary.Reasoning.Inference setoid
\end{code}
%<*partial-auto>
\begin{code}
 lemma : ∀ x y → x + y * 1 + 3 ≈ 2 + 1 + y + x
 lemma x y =
   begin
     x + y * 1 + 3    ≈⟨ +-comm (x + y * 1) 3 ⟩
     3 + (x + y * 1)  ≈⟨ solveOver (x ∷ y ∷ []) Nat.ring ⟩
     3 + y + x        ≡⟨⟩
     2 + 1 + y + x    ∎
\end{code}
%</partial-auto>
\begin{code}
module ExprDef where
  open import Data.Fin
\end{code}
%<*expr-def>
\begin{code}
  data Expr  {ℓ} (A : Set ℓ) (n : ℕ) : Set ℓ where
    Κ    : A → Expr A n
    I    : Fin n → Expr A n
    _⊕_  : Expr A n → Expr A n → Expr A n
    _⊗_  : Expr A n → Expr A n → Expr A n
    ⊝_   : Expr A n → Expr A n
\end{code}
%</expr-def>
\begin{code}
open import Data.Nat.Properties
open import Polynomial.Simple.AlmostCommutativeRing
import Relation.Binary.PropositionalEquality as ≡
open import Data.Maybe using (Maybe; just; nothing)
NatRing : AlmostCommutativeRing _ _
NatRing = fromCommutativeSemiring *-+-commutativeSemiring λ { zero → just ≡.refl ; (suc x) → nothing}
open AlmostCommutativeRing NatRing
open import Polynomial.Simple.Reflection
open import Data.List
open import Relation.Nullary
open import Data.Unit
\end{code}
%<*refl-lemma>
\begin{code}
lemma : ∀ x y
      → x + y * 1 + 3 ≈ 2 + 1 + x + y
lemma = solve NatRing
\end{code}
%</refl-lemma>
\begin{code}
nonlemma : ∀ x y →
\end{code}
%<*wrong-lemma>
\begin{code}
          x + y * 1 + 3 ≈ 2 + 1 + y + y
\end{code}
%</wrong-lemma>
\begin{code}
         → ⊤
nonlemma _ _ _ = tt
-- (y ℕ.+ 0 ℕ.* y) ℕ.* 1 != x
\end{code}
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
%<*nat-term>
\begin{code}
natTerm : ℕ → Term
natTerm zero = con (quote ℕ.zero) []
natTerm (suc i) =
  con
    (quote suc)
    (arg (arg-info visible relevant)
    (natTerm i) ∷ [])
\end{code}
%</nat-term>

%<*occ-of>
\begin{code}
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
%<*occ-wrong>
\begin{code}
infixl 6 _plus_
_plus_ : ℕ → ℕ → ℕ
_plus_ = _+_

occWrong :
  occurencesOf _+_
    (λ x y → 2 plus 1 plus x plus y)
  ≡ 0
occWrong = refl
\end{code}
%</occ-wrong>
%<*synonyms>
\begin{code}
infixr 5 _⟨∷⟩_ _⟅∷⟆_
pattern _⟨∷⟩_ x xs =
  arg (arg-info visible relevant) x ∷ xs
pattern _⟅∷⟆_ x xs =
  arg (arg-info hidden relevant) x ∷ xs
\end{code}
%</synonyms>
\begin{code}
open import Polynomial.Expr
open import Data.List
open import Function
\end{code}
%<*infer-hidden>
\begin{code}
infixr 5 _⋯⟅∷⟆_
_⋯⟅∷⟆_  : ℕ
        → List (Arg Term)
        → List (Arg Term)
zero   ⋯⟅∷⟆ xs = xs
suc i  ⋯⟅∷⟆ xs = unknown ⟅∷⟆ i ⋯⟅∷⟆ xs
\end{code}
%</infer-hidden>
%<*numvars>
\begin{code}
module _ (numVars : ℕ) where
\end{code}
%</numvars>
%<*expr-const-ast>
\begin{code}
 constExpr : Term → Term
 constExpr x =
   quote Κ ⟨ con ⟩
     2 ⋯⟅∷⟆
     natTerm numVars ⟅∷⟆
     x ⟨∷⟩
     []
\end{code}
%</expr-const-ast>
\begin{code}
 mutual
\end{code}
%<*op-build>
\begin{code}
  getBinOp : Name
           → List (Arg Term)
           → Term
  getBinOp nm (x ⟨∷⟩ y ⟨∷⟩ []) =
    nm ⟨ con ⟩
      2 ⋯⟅∷⟆
      natTerm numVars ⟅∷⟆
      toExpr x ⟨∷⟩
      toExpr y ⟨∷⟩
      []
  getBinOp nm (x ∷ xs) = getBinOp nm xs
  getBinOp _ _ = unknown

  getUnOp : Name
          → List (Arg Term)
          → Term
  getUnOp nm (x ⟨∷⟩ []) =
    nm ⟨ con ⟩
      2 ⋯⟅∷⟆
      natTerm numVars ⟅∷⟆
      toExpr x ⟨∷⟩
      []
  getUnOp nm (x ∷ xs) = getUnOp nm xs
  getUnOp _ _ = unknown
\end{code}
%</op-build>
%<*to-expr>
\begin{code}
  toExpr : Term → Term
  toExpr (def (quote AlmostCommutativeRing._+_)  xs) = getBinOp (quote _⊕_) xs
  toExpr (def (quote AlmostCommutativeRing._*_)  xs) = getBinOp (quote _⊗_) xs
  toExpr (def (quote AlmostCommutativeRing.-_)   xs) = getUnOp (quote ⊝_) xs
  toExpr v@(var x _) with x ℕ.<? numVars
  ... | yes p = v
  ... | no ¬p = constExpr v
  toExpr t = constExpr t
\end{code}
%</to-expr>
