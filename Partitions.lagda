\begin{code}
module Partitions where

open import Data.Nat using (ℕ; _+_)
open import Data.Product using (Σ; proj₁; proj₂; _×_; _,_)
open import Data.Unit
open import Function using (_∘_; _|>_; const)
open import Level
open import Relation.Unary
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)

\end{code}
In where I try to figure out what's going on in the lecture notes
https://github.com/pigworker/ProgrammerCommaCon/blob/master/CS410-19/Exercise/Two.agda

|CutInto| is about cutting something fairly arbitrary into finitely many pieces of
given shape |I|. It's finite because given some evidence of type |Cut| of a cut,
we get a (necessarily finite) |List| of items of |I| that are ``part of'' the cut.

So let's lift that finiteness condition, and instead have |Enum| ('Enum'eration) many
things. We don't

\begin{code}
record CutInto (I : Set) : Set₁ where
  field
    Cut : Set
    Enum : Set
    pieces : Cut → Enum → I

open CutInto
\end{code}

So a |Partition| into |I| shaped pieces of |O| is:
\begin{code}
Partition : Set → Set → Set₁
Partition I O = O → CutInto I
\end{code}

We should do the length example, to show it works the same. Partitioning by
Length means to split into |Two|
\begin{code}
data Two : Set where ze on : Two

Length : Partition ℕ ℕ
Length n = record
  { Cut = Σ (Two → ℕ) (λ p → p ze + p on ≡ n)
  ; Enum = Two
  ; pieces = proj₁
  }
\end{code}

Given a predicate P, |All P enum| expresses that |P| holds
for all |X| that |E| points to.  Generalization of the |List| version.
\begin{code}
All : {E X : Set} (P : X → Set) → (E → X) → Set
All {E} P enum = (e : E) → P (enum e)
\end{code}

Given a |Partition| and a predicate on the shape, we can build a
predicate on the pieces of the partition.
\begin{code}
_SplitOver_ : {I O : Set} → Pred I 0ℓ → Partition I O → Pred O 0ℓ
P SplitOver Part = λ o → Σ (Cut (Part o)) (λ c → pieces (Part o) c |> All P)
\end{code}

There's categorical happenings, show that too.
\begin{code}
idPart : ∀ {I} → Partition I I
idPart = λ i → record { Cut = ⊤ ; Enum = ⊤ ; pieces = λ _ _ → i }

infix 4 _∘P_
_∘P_ : ∀ {I J K} → Partition I J → Partition J K → Partition I K
_∘P_ {I} P Q k = record
  { Cut = C′
  ; Enum = E′
  ; pieces = p
  }
  where
  cQ = Cut (Q k)
  eQ = Enum (Q k)
  C′ : Set
  C′ = Σ cQ (λ c → (Σ eQ (λ e → Cut (P (pieces (Q k) c e)))))
  E′ : Set
  E′ = Σ cQ (λ c → (e : eQ) → Enum (P (pieces (Q k) c e)))
  p : C′ → E′ → I
  p (c₁ , e₁ , p₁) e = pieces (P (pieces (Q k) c₁ e₁)) p₁ {!proj₂ e e₁!}
\end{code}

And now check that splitting over |idPart| is a left and right identity
for a predicate.
\begin{code}
right-id : ∀ {I} {P : I → Set} → ∀[ P ⇒ (P SplitOver idPart) ]
right-id pi = tt , const pi

left-id :  ∀ {I} {P : I → Set} → ∀[ (P SplitOver idPart) ⇒ P ]
left-id pi = proj₂ pi tt

assoc : ∀ {I J K} (IJ : Partition I J) (JK : Partition J K) {P : I → Set} →
  ∀[ P SplitOver (IJ ∘P JK) ⇒ ((P SplitOver IJ) SplitOver JK) ]
assoc IJ JK {P} {i} ((cIJ , eIJ , cJK) , e) = cIJ , {!!}
\end{code}
