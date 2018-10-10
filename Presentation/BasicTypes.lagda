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
open import Data.List hiding (length; head)

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
