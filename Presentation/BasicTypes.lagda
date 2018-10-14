\begin{code}
module Presentation.BasicTypes where

open import Data.Nat
\end{code}
%<*xint>
\begin{code}
x : ℕ
\end{code}
%</xint>
%<*xprf>
\begin{code}
x = 1
\end{code}
%</xprf>
\begin{code}
open import Data.List hiding (length; head; reverse)

pattern 1+ x = suc x
\end{code}
%<*fib>
\begin{code}
fib : ℕ → ℕ
fib 0            = 0
fib (1+ 0)       = 1+ 0
fib (1+ (1+ n))  = fib (1+ n) + fib n
\end{code}
%</fib>
%<*length>
\begin{code}
length : {A : Set} → List A → ℕ
length [] = 0
length (x ∷ xs) = 1 + length xs
\end{code}
%</length>
\begin{code}
{-# TERMINATING #-}
\end{code}
%<*headty>
\begin{code}
head : {A : Set} → List A → A
\end{code}
%</headty>
%<*head1>
\begin{code}
head (x ∷ xs) = x
\end{code}
%</head1>
%<*head2>
\begin{code}
head [] = head []
\end{code}
%</head2>
%<*false>
\begin{code}
¬ : ∀ {ℓ} → Set ℓ → Set _
¬ A = A → {B : Set} → B
\end{code}
%</false>
%<*head-not>
\begin{code}
head-doesn't-exist : ¬ ({A : Set} → List A → A)
head-doesn't-exist head = head []
\end{code}
%</head-not>
\begin{code}
module ProofSigs where
  open import Relation.Binary.PropositionalEquality
  reverse : ℕ → ℕ
  reverse x = x
\end{code}
%<*reverse-props>
\begin{code}
  reverse-involution : ∀ xs → reverse (reverse xs) ≡ xs
\end{code}
%</reverse-props>
\begin{code}
  reverse-involution xs = refl
\end{code}
%<*bool-def>
\begin{code}
data Bool : Set where
  true   : Bool
  false  : Bool
\end{code}
%</bool-def>
%<*bot-def>
\begin{code}
data ⊥ : Set where
\end{code}
%</bot-def>
%<*poe-to-bot>
\begin{code}
lnc : ⊥ → {A : Set} → A
lnc ()
\end{code}
%</poe-to-bot>
%<*top-def>
\begin{code}
data ⊤ : Set where
  tt : ⊤
\end{code}
%</top-def>
\begin{code}
module Impl where
  data A : Set where
  data B : Set where
  implication :
\end{code}
%<*impl>
\begin{code}
    A → B
\end{code}
%</impl>
\begin{code}
  implication ()
\end{code}
