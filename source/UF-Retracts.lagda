\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF-Retracts where

open import SpartanMLTT
open import UF-Base
open import UF-Subsingletons

has-section : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
has-section r = Σ \s → r ∘ s ∼ id

has-retraction : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
has-retraction s = Σ \r → r ∘ s ∼ id

has-retraction-lc : ∀ {U V} {X : U ̇} {Y : V ̇} (s : X → Y)
                 → has-retraction s → left-cancellable s
has-retraction-lc s (r , rs) {x} {x'} p = (rs x)⁻¹ ∙ ap r p ∙ rs x'

retract_of_ : ∀ {U V} → U ̇ → V ̇ → U ⊔ V ̇
retract Y of X = Σ \(r : X → Y) → has-section r

retract-of-singleton : ∀ {U V} {X : U ̇} {Y : V ̇}
                    → retract Y of X
                    → is-singleton X
                    → is-singleton Y
retract-of-singleton (r , s , rs) (c , φ) = r c , (λ y → ap r (φ (s y)) ∙ rs y)

identity-retraction : ∀ {U} {X : U ̇} → retract X of X
identity-retraction = id , (id , λ x → refl)

has-section-closed-under-∼ : ∀ {U V} {X : U ̇} {Y : V ̇} (f g : X → Y) → has-section f →  g ∼ f  → has-section g
has-section-closed-under-∼ {U} {V} {X} {Y} f g (s , fs) h = (s , λ y → g (s y) ≡⟨ h (s y) ⟩ f (s y) ≡⟨ fs y ⟩ y ∎)

has-section-closed-under-∼' : ∀ {U V} {X : U ̇} {Y : V ̇} {f g : X → Y} → has-section f → f ∼ g → has-section g
has-section-closed-under-∼' ise h = has-section-closed-under-∼ _ _ ise (λ x → (h x)⁻¹)

has-retraction-closed-under-∼ : ∀ {U V} {X : U ̇} {Y : V ̇} (f g : X → Y) → has-retraction f →  g ∼ f  → has-retraction g
has-retraction-closed-under-∼ {U} {V} {X} {Y} f g (r , rf) h = (r , λ x → r (g x) ≡⟨ ap r (h x) ⟩ r (f x) ≡⟨ rf x ⟩ x ∎)

has-retraction-closed-under-∼' : ∀ {U V} {X : U ̇} {Y : V ̇} {f g : X → Y} → has-retraction f → f ∼ g → has-retraction g
has-retraction-closed-under-∼' ise h = has-retraction-closed-under-∼ _ _ ise (λ x → (h x)⁻¹)

\end{code}

Surjection expressed in Curry-Howard logic amounts to retraction.

\begin{code}

retraction : ∀ {U V} {X : U ̇} {Y : V ̇} → (f : X → Y) → U ⊔ V ̇
retraction f = ∀ y → Σ \x → f x ≡ y

retract_Of_ : ∀ {U V} → U ̇ → V ̇ → U ⊔ V ̇
retract Y Of X = Σ \(f : X → Y) → retraction f

retract-of-retract-Of : ∀ {U V} {X : U ̇} {Y : V ̇} → retract Y of X → retract Y Of X
retract-of-retract-Of {U} {V} {X} {Y} (f , φ)= (f , hass)
 where
  hass : (y : Y) → Σ \(x : X) → f x ≡ y
  hass y = pr₁ φ y , pr₂ φ y

retract-Of-retract-of : ∀ {U V} {X : U ̇} {Y : V ̇} → retract Y Of X → retract Y of X
retract-Of-retract-of {U} {V} {X} {Y} (f , hass) = (f , φ)
 where
  φ : Σ \(s : Y → X) → f ∘ s ∼ id
  φ = (λ y → pr₁ (hass y)) , λ y → pr₂ (hass y)

retracts-compose : ∀ {U V W} {X : U ̇} {Y : V ̇} {Z : W ̇}
                 → retract Y of X → retract Z of Y → retract Z of X
retracts-compose (r , (s , rs)) (r' , (s' , rs')) = r' ∘ r ,
                                                    (s ∘ s' , λ z → ap r' (rs (s' z)) ∙ rs' z)


×-retract : ∀ {U V W T} {X : U ̇} {Y : V ̇} {A : W ̇} {B : T ̇}
           → retract X of A
           → retract Y of B
           → retract (X × Y) of (A × B)
×-retract {U} {V} {W} {T} {X} {Y} {A} {B} (r , s , rs) (t , u , tu) = f , g , fg
 where
  f : A × B → X × Y
  f (a , b) = (r a , t b)
  g : X × Y → A × B
  g (x , y) = s x , u y
  fg : (z : X × Y) → f (g z) ≡ z
  fg (x , y) = ×-≡ (rs x) (tu y)

+-retract : ∀ {U V W T} {X : U ̇} {Y : W ̇} {A : V ̇} {B : T ̇}
           → retract X of A
           → retract Y of B
           → retract (X + Y) of (A + B)
+-retract {U} {V} {W} {T} {X} {Y} {A} {B} (r , s , rs) (t , u , tu) = f , g , fg
 where
  f : A + B → X + Y
  f (inl a) = inl(r a)
  f (inr b) = inr(t b)
  g : X + Y → A + B
  g (inl x) = inl(s x)
  g (inr y) = inr(u y)
  fg : (p : X + Y) → f (g p) ≡ p
  fg (inl x) = ap inl (rs x)
  fg (inr y) = ap inr (tu y)

+'-retract-of-+ : ∀ {U} {X Y : U ̇}
           → retract (X +' Y) of (X + Y)
+'-retract-of-+ {U} {X} {Y} = f , g , fg
 where
  f : X + Y → X +' Y
  f (inl x) = ₀ , x
  f (inr y) = ₁ , y
  g : X +' Y → X + Y
  g (₀ , x) = inl x
  g (₁ , y) = inr y
  fg : (z : X +' Y) → f (g z) ≡ z
  fg (₀ , x) = refl
  fg (₁ , y) = refl

+'-retract : ∀ {U V} {X Y : U ̇} {A B : V ̇}
           → retract X of A
           → retract Y of B
           → retract (X +' Y) of (A +' B)
+'-retract {U} {V} {X} {Y} {A} {B} (r , s , rs) (t , u , tu) = f , g , fg
 where
  f : A +' B → X +' Y
  f (₀ , a) = ₀ , r a
  f (₁ , b) = ₁ , t b
  g : X +' Y → A +' B
  g (₀ , x) = ₀ , s x
  g (₁ , y) = ₁ , u y
  fg : (p : X +' Y) → f (g p) ≡ p
  fg (₀ , x) = ap (λ - → (₀ , -)) (rs x)
  fg (₁ , y) = ap (λ - → (₁ , -)) (tu y)

Σ-reindex-retract : ∀ {U V W} {X : U ̇} {Y : V ̇} {A : X → W ̇} (r : Y → X)
                  → has-section r → retract (Σ A) of (Σ (A ∘ r))
Σ-reindex-retract {U} {V} {W} {X} {Y} {A} r (s , rs) = γ , φ , γφ
 where
  γ : (Σ \(y : Y) → A (r y)) → Σ A
  γ (y , a) = (r y , a)
  φ : Σ A → Σ \(y : Y) → A (r y)
  φ (x , a) = (s x , back-transport A (rs x) a)
  γφ : (σ : Σ A) → γ (φ σ) ≡ σ
  γφ (x , a) = to-Σ-≡ (rs x , p)
   where
    p : transport A (rs x) (back-transport A (rs x) a) ≡ a
    p = back-and-forth-transport (rs x)

Σ-retract : ∀ {U V W} {X : U ̇} (A : X → V ̇) (B : X → W ̇)
          → ((x : X) → retract (A x) of (B x))
          → retract (Σ A) of (Σ B)
Σ-retract {U} {V} {W} {X} A B ρ = NatΣ R , NatΣ S , rs
 where
  R : (x : X) → B x → A x
  R x = pr₁(ρ x)
  S : (x : X) → A x → B x
  S x = pr₁(pr₂(ρ x))
  RS : (x : X) (a : A x) → R x (S x a) ≡ a
  RS x = pr₂(pr₂(ρ x))
  rs : (σ : Σ A) → NatΣ R (NatΣ S σ) ≡ σ
  rs (x , a) = to-Σ-≡' (RS x a)

retract-𝟙+𝟙-of-𝟚 : retract 𝟙 + 𝟙 of 𝟚
retract-𝟙+𝟙-of-𝟚 = f , (g , fg)
 where
  f : 𝟚 → 𝟙 {U₀} + 𝟙 {U₀}
  f = 𝟚-cases (inl *) (inr *)
  g : 𝟙 + 𝟙 → 𝟚
  g = cases (λ x → ₀) (λ x → ₁)
  fg : (x : 𝟙 + 𝟙) → f (g x) ≡ x
  fg (inl *) = refl
  fg (inr *) = refl

\end{code}

TODO. Several retractions here are actually equivalences. So some code
should be generalized and moved to an equivalences module. Similarly,
some retracts proved here are also shown as equivalences in other
modules, and hence there is some amount of repetition that should be
removed. This is the result of (1) merging initially independent
developments, and (2) work over many years with uncontrolled growth.

\begin{code}

Σ-retract₂ : ∀ {U V W T} {X : U ̇} {Y : X → V ̇} {A : W ̇} {B : T ̇}
           → retract X of A
           → ((x : X) → retract  (Y x) of B)
           → retract (Σ Y) of (A × B)
Σ-retract₂ {U} {V} {W} {T} {X} {Y} {A} {B} (r , s , rs) R = f , g , gf
 where
  φ : (x : X) → B → Y x
  φ x = pr₁ (R x)
  γ : (x : X) → Y x → B
  γ x = pr₁ (pr₂ (R x))
  φγ : (x : X) → (y : Y x) → φ x (γ x y) ≡ y
  φγ x = pr₂ (pr₂ (R x))
  f : A × B → Σ Y
  f (a , b) = r a , φ (r a) b
  g : Σ Y → A × B
  g (x , y) = s x , γ x y
  gf : (z : Σ Y) → f (g z) ≡ z
  gf (x , y) = to-Σ-≡ (rs x , l (rs x))
   where
    l : {x' : X} (p : x' ≡ x) → transport Y p (φ x' (γ x y)) ≡ y
    l refl = φγ x y

retract-𝟙+𝟙-of-ℕ : retract 𝟙 + 𝟙 of ℕ
retract-𝟙+𝟙-of-ℕ = r , s , rs
 where
  r : ℕ → 𝟙 + 𝟙
  r zero = inl *
  r (succ _) = inr *
  s : 𝟙 + 𝟙 → ℕ
  s (inl *) = zero
  s (inr *) = succ zero
  rs : (z : 𝟙 {U₀} + 𝟙 {U₀}) → r (s z) ≡ z
  rs (inl *) = refl
  rs (inr *) = refl

\end{code}
