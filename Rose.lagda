\begin{code}
module Rose where
open import Data.List
open import Agda.Builtin.Size
module Unsized where
\end{code}
%<*rose>
\begin{code}
  infixr 6 _&_
  data Tree {a} (A : Set a) : Set a where
    _&_ : A → List (Tree A) → Tree A
\end{code}
%</rose>
\begin{code}
  module Levels1 where
\end{code}
%<*nonterminating-rose>
\begin{code}
    {-# TERMINATING #-}
    levels : ∀ {a} {A : Set a}
          → Tree A
          → List (List A)
    levels {A = A} tr = f tr []
      where
      f : Tree A → List (List A) → List (List A)
      f (x & xs) []        = (x ∷ [])  ∷ foldr f []  xs
      f (x & xs) (q ∷ qs)  = (x ∷ q)   ∷ foldr f qs  xs
\end{code}
%</nonterminating-rose>

\begin{code}
  module Levels2 where
\end{code}
%<*terminating-rose>
\begin{code}
    levels : ∀ {a} {A : Set a}
          → Tree A
          → List (List A)
    levels {A = A} (t & tr) = (t ∷ []) ∷ f tr []
      where
      f : List (Tree A)
        → List (List A)
        → List (List A)
      f []              qs        = qs
      f (x & xs ∷ xxs)  []        = (x ∷ [])  ∷ f xs []
      f (x & xs ∷ xxs)  (q ∷ qs)  = (x ∷ q)   ∷ f xs qs
\end{code}
%</terminating-rose>
%<*sized-rose>
\begin{code}
infixr 6 _&_
data Tree {a} (A : Set a)
     : {i : Size} →  Set a where
  _&_ : ∀ {i}
      → A
      → List (Tree A {i})
      → Tree A {↑ i}
\end{code}
%</sized-rose>
%<*sized-rose-levels>
\begin{code}
levels : ∀ {a} {A : Set a}
       → Tree A
       → List (List A)
levels {A = A} tr = f tr []
  where
  f : ∀ {i}
    → Tree A {i}
    → List (List A)
    → List (List A)
  f (x & xs) []        = (x ∷ [])  ∷ foldr f []  xs
  f (x & xs) (q ∷ qs)  = (x ∷ q)   ∷ foldr f qs  xs
\end{code}
%</sized-rose-levels>
