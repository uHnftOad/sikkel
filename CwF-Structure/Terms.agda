--------------------------------------------------
-- Terms
--------------------------------------------------

module CwF-Structure.Terms where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality; Extensionality; subst₂)

open import Helpers
open import CwF-Structure.Contexts
open import CwF-Structure.Types

infix 1 _≅ᵗᵐ_


--------------------------------------------------
-- Definition of terms

record Tm {ℓ} (Γ : Ctx ℓ) (T : Ty Γ) : Set ℓ where
  constructor MkTm
  field
    term : (n : ℕ) (γ : Γ ⟨ n ⟩) → T ⟨ n , γ ⟩
    naturality : ∀ {m n} (ineq : m ≤ n) {γn : Γ ⟨ n ⟩} {γm : Γ ⟨ m ⟩} (eq : Γ ⟪ ineq ⟫ γn ≡ γm) →
                 T ⟪ ineq , eq ⟫ (term n γn) ≡ term m γm
open Tm public

_⟨_,_⟩' : {Γ : Ctx ℓ} {T : Ty Γ} → Tm Γ T → (n : ℕ) → (γ : Γ ⟨ n ⟩) → T ⟨ n , γ ⟩
t ⟨ n , γ ⟩' = term t n γ


--------------------------------------------------
-- Equivalence of terms

record _≅ᵗᵐ_ {Γ : Ctx ℓ} {T : Ty Γ} (t s : Tm Γ T) : Set ℓ where
  field
    eq : ∀ {n} γ → t ⟨ n , γ ⟩' ≡ s ⟨ n , γ ⟩'
open _≅ᵗᵐ_ public

≅ᵗᵐ-refl : {Γ : Ctx ℓ} {T : Ty Γ} {t : Tm Γ T} → t ≅ᵗᵐ t
eq (≅ᵗᵐ-refl {t = t}) _ = refl

≅ᵗᵐ-sym : {Γ : Ctx ℓ} {T : Ty Γ} {t s : Tm Γ T} → t ≅ᵗᵐ s → s ≅ᵗᵐ t
eq (≅ᵗᵐ-sym t=s) γ = sym (eq t=s γ)

≅ᵗᵐ-trans : {Γ : Ctx ℓ} {T : Ty Γ} {t1 t2 t3 : Tm Γ T} → t1 ≅ᵗᵐ t2 → t2 ≅ᵗᵐ t3 → t1 ≅ᵗᵐ t3
eq (≅ᵗᵐ-trans t1=t2 t2=t3) γ = trans (eq t1=t2 γ) (eq t2=t3 γ)

module ≅ᵗᵐ-Reasoning {Γ : Ctx ℓ} {T : Ty Γ} where
  infix  3 _∎
  infixr 2 _≅⟨⟩_ step-≅ step-≅˘
  infix  1 begin_

  begin_ : ∀ {t s : Tm Γ T} → t ≅ᵗᵐ s → t ≅ᵗᵐ s
  begin_ t=s = t=s

  _≅⟨⟩_ : ∀ (t {s} : Tm Γ T) → t ≅ᵗᵐ s → t ≅ᵗᵐ s
  _ ≅⟨⟩ t=s = t=s

  step-≅ : ∀ (t1 {t2 t3} : Tm Γ T) → t1 ≅ᵗᵐ t2 → t2 ≅ᵗᵐ t3 → t1 ≅ᵗᵐ t3
  step-≅ _ t1≅t2 t2≅t3 = ≅ᵗᵐ-trans t1≅t2 t2≅t3

  step-≅˘ : ∀ (t1 {t2 t3} : Tm Γ T) → t2 ≅ᵗᵐ t3 → t2 ≅ᵗᵐ t1 → t1 ≅ᵗᵐ t3
  step-≅˘ _ t2≅t3 t2≅t1 = ≅ᵗᵐ-trans (≅ᵗᵐ-sym t2≅t1) t2≅t3

  _∎ : ∀ (t : Tm Γ T) → t ≅ᵗᵐ t
  _∎ _ = ≅ᵗᵐ-refl

  syntax step-≅  t1 t2≅t3 t1≅t2 = t1 ≅⟨  t1≅t2 ⟩ t2≅t3
  syntax step-≅˘ t1 t2≅t3 t2≅t1 = t1 ≅˘⟨ t2≅t1 ⟩ t2≅t3


--------------------------------------------------
-- Reindexing maps (cf. Dybjer's internal type theory)

convert-term : {Γ : Ctx ℓ} {T S : Ty Γ} → (T ↣ S) → Tm Γ T → Tm Γ S
term (convert-term η t) n γ = func η (t ⟨ n , γ ⟩')
naturality (convert-term {T = T}{S} η t) m≤n eγ =
  begin
    S ⟪ m≤n , eγ ⟫ func η (t ⟨ _ , _ ⟩')
  ≡⟨ naturality η _ ⟩
    func η (T ⟪ m≤n , eγ ⟫ (t ⟨ _ , _ ⟩'))
  ≡⟨ cong (func η) (naturality t _ _) ⟩
    func η (t ⟨ _ , _ ⟩') ∎
  where open ≡-Reasoning

convert-term-cong : {Γ : Ctx ℓ} {T S : Ty Γ} (η : T ↣ S) {t t' : Tm Γ T} →
                    t ≅ᵗᵐ t' → convert-term η t ≅ᵗᵐ convert-term η t'
eq (convert-term-cong η t=t') γ = cong (func η) (eq t=t' γ)

ι[_]_ : {Γ : Ctx ℓ} {T S : Ty Γ} → T ≅ᵗʸ S → Tm Γ S → Tm Γ T
ι[ T=S ] s = convert-term (to T=S) s

ι-cong : {Γ : Ctx ℓ} {T S : Ty Γ} (T=S : T ≅ᵗʸ S) {s s' : Tm Γ S} →
         s ≅ᵗᵐ s' → ι[ T=S ] s ≅ᵗᵐ ι[ T=S ] s'
ι-cong T=S s=s' = convert-term-cong (to T=S) s=s'

ι-refl : {Γ : Ctx ℓ} {T : Ty Γ} (t : Tm Γ T) → ι[ ≅ᵗʸ-refl ] t ≅ᵗᵐ t
eq (ι-refl t) _ = refl

ι-symˡ : {Γ : Ctx ℓ} {T S : Ty Γ} (T=S : T ≅ᵗʸ S) (s : Tm Γ S) →
         ι[ ≅ᵗʸ-sym T=S ] (ι[ T=S ] s) ≅ᵗᵐ s
eq (ι-symˡ T=S s) γ = eq (isoʳ T=S) (s ⟨ _ , γ ⟩')

ι-symʳ : {Γ : Ctx ℓ} {T S : Ty Γ} (T=S : T ≅ᵗʸ S) (t : Tm Γ T) →
         ι[ T=S ] (ι[ ≅ᵗʸ-sym T=S ] t) ≅ᵗᵐ t
eq (ι-symʳ T=S t) γ = eq (isoˡ T=S) (t ⟨ _ , γ ⟩')

ι⁻¹[_]_ : {Γ : Ctx ℓ} {T S : Ty Γ} → T ≅ᵗʸ S → Tm Γ T → Tm Γ S
ι⁻¹[ T=S ] t = ι[ ≅ᵗʸ-sym T=S ] t

ι-trans : {Γ : Ctx ℓ} {T S R : Ty Γ} (T=S : T ≅ᵗʸ S) (S=R : S ≅ᵗʸ R) (r : Tm Γ R) →
          ι[ ≅ᵗʸ-trans T=S S=R ] r ≅ᵗᵐ ι[ T=S ] (ι[ S=R ] r)
eq (ι-trans T=S S=R r) γ = refl


--------------------------------------------------
-- Substitution of terms

_[_]' : {Δ Γ : Ctx ℓ} {T : Ty Γ} → Tm Γ T → (σ : Δ ⇒ Γ) → Tm Δ (T [ σ ])
term (t [ σ ]') n δ = t ⟨ n , func σ δ ⟩'
naturality (t [ σ ]') m≤n eγ = naturality t m≤n _

tm-subst-cong-tm : {Δ Γ : Ctx ℓ} (σ : Δ ⇒ Γ) {T : Ty Γ} {t s : Tm Γ T} → t ≅ᵗᵐ s → t [ σ ]' ≅ᵗᵐ s [ σ ]'
eq (tm-subst-cong-tm σ t=s) δ = eq t=s (func σ δ)

convert-subst-commute : {Δ Γ : Ctx ℓ} (σ : Δ ⇒ Γ) {T S : Ty Γ} (η : T ↣ S) (t : Tm Γ T) →
                        convert-term (ty-subst-map σ η) (t [ σ ]') ≅ᵗᵐ (convert-term η t) [ σ ]'
eq (convert-subst-commute σ η t) δ = refl

ι-subst-commute : {Δ Γ : Ctx ℓ} (σ : Δ ⇒ Γ) {T S : Ty Γ} (T=S : T ≅ᵗʸ S) (s : Tm Γ S) →
                  ι[ ty-subst-cong-ty σ T=S ] (s [ σ ]') ≅ᵗᵐ (ι[ T=S ] s) [ σ ]'
ι-subst-commute σ T=S s = convert-subst-commute σ (to T=S) s

tm-subst-cong-subst : {Δ Γ : Ctx ℓ} {σ τ : Δ ⇒ Γ} {T : Ty Γ} (t : Tm Γ T) →
                      (σ=τ : σ ≅ˢ τ) → t [ σ ]' ≅ᵗᵐ ι[ ty-subst-cong-subst σ=τ T ] (t [ τ ]')
eq (tm-subst-cong-subst {σ = σ}{τ}{T} t σ=τ) δ = sym (naturality t ≤-refl _)

tm-subst-id : {Γ : Ctx ℓ} {T : Ty Γ} (t : Tm Γ T) → t [ id-subst Γ ]' ≅ᵗᵐ ι[ ty-subst-id T ] t
eq (tm-subst-id t) _ = refl

tm-subst-comp : {Δ Γ Θ : Ctx ℓ} {T : Ty Θ} (t : Tm Θ T) (τ : Γ ⇒ Θ) (σ : Δ ⇒ Γ) →
                t [ τ ]' [ σ ]' ≅ᵗᵐ ι[ ty-subst-comp T τ σ ] (t [ τ ⊚ σ ]')
eq (tm-subst-comp t τ σ) _ = refl
