Martin Escardo 2011.

Our Spartan (intensional) Martin-Löf type theory has a countable tower
of universes, the empty type ∅, the unit type 𝟙, product types Π, sum
types Σ (and hence binary product types _×_), sum types _+_.
identity types _≡_.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module SpartanMLTT where

open import Universes public

\end{code}

The module Universes allows us to write e.g. the following instead of

    Π : ∀ {i j} {X : Set i} (Y : X → Set j) → Set (i ⊔ j)
    Π Y = (x : _) → Y x

\begin{code}

Π : {X : U ̇} (Y : X → V ̇) → U ⊔ V ̇
Π Y = (x : _) → Y x

syntax Π {A} (λ x → B) = Π（ x ∶ A ） B

\end{code}

Identity and dependent function composition:

\begin{code}

id : {X : U ̇} → X → X
id x = x

_∘_ : {X : U ̇} {Y : V ̇} {Z : Y → W ̇}
    → ((y : Y) → Z y)
    → (f : X → Y) (x : X) → Z (f x)
g ∘ f = λ x → g(f x)

\end{code}

Empty type.

\begin{code}

data 𝟘 {U} : U ̇ where

unique-from-𝟘 : {A : U ̇} → 𝟘 {V} → A
unique-from-𝟘 = λ ()

𝟘-elim = unique-from-𝟘

\end{code}

The one-element type is defined by induction with one case:

\begin{code}

data 𝟙 {U} : U ̇ where
 * : 𝟙

unique-to-𝟙 : {A : U ̇} → A → 𝟙 {V}
unique-to-𝟙 {U} {V} a = * {V}

open import Sigma public

\end{code}

Binary sums

\begin{code}

data _+_ {U V} (X : U ̇) (Y : V ̇) : U ⊔ V ̇ where
  inl : X → X + Y
  inr : Y → X + Y

dep-cases : {X : U ̇} {Y : V ̇} {A : X + Y → W ̇}
          → ((x : X) → A(inl x))
          → ((y : Y) → A(inr y))
          → ((z : X + Y) → A z)
dep-cases f g (inl x) = f x
dep-cases f g (inr y) = g y

cases : {X : U ̇} {Y : V ̇} {A : W ̇} → (X → A) → (Y → A) → X + Y → A
cases = dep-cases

Cases : {X : U ̇} {Y : V ̇} {A : W ̇} → X + Y → (X → A) → (Y → A) → A
Cases z f g = cases f g z

+-commutative : {A : U ̇} {B : V ̇} → A + B → B + A
+-commutative = cases inr inl

\end{code}

Some basic Curry--Howard logic.

\begin{code}

¬_ : U ̇ → U ̇
¬ A = A → 𝟘 {U₀}

is-empty : U ̇ → U ̇
is-empty = ¬_

decidable : U ̇ → U ̇
decidable A = A + ¬ A

_⇔_ : U ̇ → V ̇ → U ⊔ V ̇
A ⇔ B = (A → B) × (B → A)

dual : {X : U ̇} {Y : V ̇} (R : W ̇) → (X → Y) → (Y → R) → (X → R)
dual R f p = p ∘ f

contrapositive : {A : U ̇} {B : V ̇} → (A → B) → ¬ B → ¬ A
contrapositive = dual _

¬¬ : U ̇ → U ̇
¬¬ A = ¬(¬ A)

¬¬-functor : {A : U ̇} {B : V ̇} → (A → B) → ¬¬ A → ¬¬ B
¬¬-functor = contrapositive ∘ contrapositive

double-negation-intro : {A : U ̇} → A → ¬¬ A
double-negation-intro x u = u x

three-negations-imply-one : {A : U ̇} → ¬(¬¬ A) → ¬ A
three-negations-imply-one = contrapositive double-negation-intro

double-negation-unshift : {X : U ̇} {A : X → V ̇} → ¬¬((x : X) → A x) → (x : X) → ¬¬(A x)
double-negation-unshift f x g = f (λ h → g (h x))

dnu : {A : U ̇} {B : V ̇} → ¬¬(A × B) → ¬¬ A × ¬¬ B
dnu φ = (¬¬-functor pr₁ φ) , (¬¬-functor pr₂ φ)

und : {A : U ̇} {B : V ̇} → ¬¬ A × ¬¬ B → ¬¬(A × B)
und (φ , γ) w = γ (λ y → φ (λ x → w (x , y)))

not-Σ-implies-Π-not : {X : U ̇} {A : X → V ̇}
                    → ¬(Σ \(x : X) → A x) → (x : X) → ¬(A x)
not-Σ-implies-Π-not = curry

Π-not-implies-not-Σ : {X : U ̇} {A : X → U ̇}
                    → ((x : X) → ¬(A x)) → ¬(Σ \(x : X) → A x)
Π-not-implies-not-Σ = uncurry

Left-fails-then-right-holds : {P : U ̇} {Q : V ̇} → P + Q → ¬ P → Q
Left-fails-then-right-holds (inl p) u = 𝟘-elim (u p)
Left-fails-then-right-holds (inr q) u = q

Right-fails-then-left-holds : {P : U ̇} {Q : V ̇} → P + Q → ¬ Q → P
Right-fails-then-left-holds (inl p) u = p
Right-fails-then-left-holds (inr q) u = 𝟘-elim (u q)

\end{code}

Equality (more in the module UF).

\begin{code}

data _≡_ {U} {X : U ̇} : X → X → U ̇ where
  refl : {x : X} → x ≡ x

lhs : {X : U ̇} {x y : X} → x ≡ y → X
lhs {U} {X} {x} {y} p = x

rhs : {X : U ̇} {x y : X} → x ≡ y → X
rhs {U} {X} {x} {y} p = y

Id : {X : U ̇} → X → X → U ̇
Id = _≡_

_≢_ : {X : U ̇} → (x y : X) → U ̇
x ≢ y = ¬(x ≡ y)

Jbased : {X : U ̇} (x : X) (A : (y : X) → x ≡ y → V ̇)
       → A x refl → (y : X) (r : x ≡ y) → A y r
Jbased x A b .x refl = b

J : {X : U ̇} (A : (x y : X) → x ≡ y → V ̇)
  → ((x : X) → A x x refl) → {x y : X} (r : x ≡ y) → A x y r
J A f {x} {y} = Jbased x (λ y p → A x y p) (f x) y

transport' : {X : U ̇} (A : X → V ̇) {x y : X}
          → x ≡ y → A x → A y
transport' A {x} {y} p a = Jbased x (λ y p → A y) a y p

transport : {X : U ̇} (A : X → V ̇) {x y : X}
          → x ≡ y → A x → A y
transport A refl = id

_∙_ : {X : U ̇} {x y z : X} → x ≡ y → y ≡ z → x ≡ z
p ∙ q = transport (Id (lhs p)) q p

_⁻¹ : {X : U ̇} → {x y : X} → x ≡ y → y ≡ x
p ⁻¹ = transport (λ - → - ≡ lhs p) p refl

ap : {X : U ̇} {Y : V ̇} (f : X → Y) {x x' : X} → x ≡ x' → f x ≡ f x'
ap f p = transport (λ - → f (lhs p) ≡ f -) p refl

back-transport : {X : U ̇} (A : X → V ̇) {x y : X} → x ≡ y → A y → A x
back-transport B p = transport B (p ⁻¹)

≢-sym : {X : U ̇} → {x y : X} → x ≢ y → y ≢ x
≢-sym u r = u(r ⁻¹)

\end{code}

Standard syntax for equality chain reasoning:

\begin{code}

_≡⟨_⟩_ : {X : U ̇} (x : X) {y z : X} → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ p ⟩ q = p ∙ q

_∎ : {X : U ̇} (x : X) → x ≡ x
_∎ _ = refl

equality-cases : {X : U ̇} {Y : V ̇} {A : W ̇} (z : X + Y)
              → ((x : X) → z ≡ inl x → A) → ((y : Y) → z ≡ inr y → A) → A
equality-cases (inl x) f g = f x refl
equality-cases (inr y) f g = g y refl

Cases-equality-l : {X : U ̇} {Y : V ̇} {A : W ̇} (f : X → A) (g : Y → A)
                 → (z : X + Y) (x : X) → z ≡ inl x → Cases z f g ≡ f x
Cases-equality-l f g .(inl x) x refl = refl

Cases-equality-r : {X : U ̇} {Y : V ̇} {A : W ̇} (f : X → A) (g : Y → A)
                 → (z : X + Y) (y : Y) → z ≡ inr y → Cases z f g ≡ g y
Cases-equality-r f g .(inr y) y refl = refl

\end{code}

Some general definitions (perhaps we need to find a better place for
this):

\begin{code}

Nat : {X : U ̇} → (X → V ̇) → (X → W ̇) → U ⊔ V ⊔ W ̇
Nat A B = Π \x → A x → B x

_∼_ : {X : U ̇} {A : X → V ̇} → Π A → Π A → U ⊔ V ̇
f ∼ g = ∀ x → f x ≡ g x

_≈_ : {X : U ̇} {x : X} {A : X → V ̇} → Nat (Id x) A → Nat (Id x) A → U ⊔ V ̇
η ≈ θ = ∀ y → η y ∼ θ y

NatΣ : {X : U ̇} {A : X → V ̇} {B : X → W ̇} → Nat A B → Σ A → Σ B
NatΣ ζ (x , a) = (x , ζ x a)

NatΠ : {X : U ̇} {A : X → V ̇} {B : X → W ̇} → Nat A B → Π A → Π B
NatΠ f g x = f x (g x) -- (S combinator from combinatory logic!)

ΠΣ-distr : {X : U ̇} {A : X → V ̇} {P : (x : X) → A x → W ̇}
         → (Π \(x : X) → Σ \(a : A x) → P x a) → Σ \(f : Π A) → Π \(x : X) → P x (f x)
ΠΣ-distr φ = (λ x → pr₁ (φ x)) , λ x → pr₂ (φ x)

ΠΣ-distr-back : {X : U ̇} {A : X → V ̇} {P : (x : X) → A x → W ̇}
              → (Σ \(f : Π A) → Π \(x : X) → P x (f x)) → Π \(x : X) → Σ \(a : A x) → P x a
ΠΣ-distr-back (f , φ) x = f x , φ x

left-cancellable : {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
left-cancellable f = ∀ {x x'} → f x ≡ f x' → x ≡ x'

left-cancellable' : {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
left-cancellable' f = ∀ x x' → f x ≡ f x' → x ≡ x'

Σ! : {X : U ̇} (A : X → V ̇) → U ⊔ V ̇
Σ! {U} {V} {X} A = (Σ \(x : X) → A x) × ((x x' : X) → A x → A x' → x ≡ x')

\end{code}

Note: Σ! is to be avoided, in favour of the contractibility of Σ, following univalent mathematics.

The following is properly proved using universes, but we don't bother
for the moment:

\begin{code}

+disjoint : {X : U ̇} {Y : V ̇} {x : X} {y : Y} → ¬(inl x ≡ inr y)
+disjoint ()

+disjoint' : {X : U ̇} {Y : V ̇} {x : X} {y : Y} → ¬(inr y ≡ inl x)
+disjoint' ()

inl-lc : {X : U ̇} {Y : V ̇} {x x' : X} → inl {U} {V} {X} {Y} x ≡ inl x' → x ≡ x'
inl-lc refl = refl

inr-lc : {X : U ̇} {Y : V ̇} {y y' : Y} → inr {U} {V} {X} {Y} y ≡ inr y' → y ≡ y'
inr-lc refl = refl

𝟙-all-* : (x : 𝟙 {U}) → x ≡ *
𝟙-all-* {U} * = refl {U}

\end{code}

General utilities to avoid (sometimes) mentioning implicit arguments
in function definitions.

\begin{code}

type-of : {X : U ̇} → X → U ̇
type-of {U} {X} x = X

universe-of : (X : U ̇) → Universe
universe-of {U} X = U

domain dom : {X : U ̇} {Y : V ̇} → (X → Y) → U ̇
domain {U} {V} {X} {Y} f = X
dom = domain

codomain cod : {X : U ̇} {Y : V ̇} → (X → Y) → V ̇
codomain {U} {V} {X} {Y} f = Y
cod = codomain

\end{code}

The two-point type (or booleans)

\begin{code}

data 𝟚 : U₀ ̇ where
 ₀ : 𝟚
 ₁ : 𝟚

𝟚-induction : {A : 𝟚 → U ̇} → A ₀ → A ₁ → (x : 𝟚) → A x
𝟚-induction r s ₀ = r
𝟚-induction r s ₁ = s

𝟚-cases : {A : U ̇} → A → A → 𝟚 → A
𝟚-cases = 𝟚-induction

\end{code}

Alternative coproduct:

\begin{code}

_+'_ : U ̇ → U ̇ → U ̇
X₀ +' X₁ = Σ \(i : 𝟚) → 𝟚-cases X₀ X₁ i

\end{code}

The natural numbers:

\begin{code}

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

rec : {X : U ̇} → X → (X → X) → (ℕ → X)
rec x f zero = x
rec x f (succ n) = f(rec x f n)

_^_ : {X : U ̇} → (X → X) → ℕ → (X → X)
(f ^ n) x = rec x f n

induction : {A : ℕ → U ̇} → A 0 → ((k : ℕ) → A k → A(succ k)) → (n : ℕ) → A n
induction base step 0 = base
induction base step (succ n) = step n (induction base step n)

a-peano-axiom : {n : ℕ} → succ n ≢ 0
a-peano-axiom ()

pred : ℕ → ℕ
pred 0 = 0
pred (succ n) = n

succ-lc : {i j : ℕ} → succ i ≡ succ j → i ≡ j
succ-lc = ap pred

succ-no-fp : (n : ℕ) → n ≡ succ n → 𝟘 {U}
succ-no-fp zero ()
succ-no-fp (succ n) p = succ-no-fp n (succ-lc p)

\end{code}

We use the following to indicate the type of a subterm:

\begin{code}

-id : (X : U ̇) → X → X
-id X x = x

syntax -id X x = x ∶ X

\end{code}

And the following to make explicit the type of hypotheses:

\begin{code}

have : {A : U ̇} {B : V ̇} → A → B → B
have _ y = y

\end{code}

Operator fixity and precedences.

\begin{code}

infixr 1 _+_
infixl 5 _∘_
infix  50 ¬_
infix  -1 _⇔_
infix  0 _≡_
infix  0 _≢_
infix  3  _⁻¹
infix  1 _∎
infixr 0 _≡⟨_⟩_
infixl 2 _∙_
infix  4  _∼_
infix 0 -id

\end{code}
