--------------------------------------------------
-- Substitution Sequences
-- 
-- This module contains some results on applying a sequence of
-- substitutions to a type or a term. The main results are
-- ty-subst-seq-cong and tm-subst-seq-cong (although the latter
-- isn't really used anywhere).
--------------------------------------------------

open import Model.BaseCategory

module Model.CwF-Structure.Reflection.SubstitutionSequence {C : BaseCategory} where

open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)

open import Model.Helpers
open import Model.CwF-Structure.Context
open import Model.CwF-Structure.Type
open import Model.CwF-Structure.Term

infixr 5 _∷_

private
  variable
    Δ Γ : Ctx C
    T : Ty Γ


-- Type of a sequence of substitutions. The order is as if you would compose them.
data _⇒⁺_ : Ctx C → Ctx C → Set₁ where
  _◼ : {Δ : Ctx C} {Γ : Ctx C} (σ : Δ ⇒ Γ) → Δ ⇒⁺ Γ
  _∷_ : ∀ {Δ : Ctx C} {Γ : Ctx C} {Θ : Ctx C} (σ : Γ ⇒ Θ) (σs : Δ ⇒⁺ Γ) → Δ ⇒⁺ Θ
    -- similar to function composition

fold : Δ ⇒⁺ Γ → Δ ⇒ Γ
fold (σ ◼) = σ
fold (σ ∷ σs) = σ ⊚ fold σs

-- Applying a sequence of substitutions to a type.
_⟦_⟧ : (T : Ty Γ) (σs : Δ ⇒⁺ Γ) → Ty Δ
T ⟦ σ ◼ ⟧ = T [ σ ]
T ⟦ σ ∷ σs ⟧ = (T [ σ ]) ⟦ σs ⟧

-- Applying a sequence of substitutions to a term.
_⟦_⟧' : (t : Tm Γ T) (σs : Δ ⇒⁺ Γ) → Tm Δ (T ⟦ σs ⟧)
t ⟦ σ ◼ ⟧' = t [ σ ]'
t ⟦ σ ∷ σs ⟧' = (t [ σ ]') ⟦ σs ⟧'

ty-subst-seq-fold : (σs : Δ ⇒⁺ Γ) (T : Ty Γ) →
                    T ⟦ σs ⟧ ≅ᵗʸ T [ fold σs ]
ty-subst-seq-fold (σ ◼) T = reflᵗʸ
ty-subst-seq-fold (σ ∷ σs) T = transᵗʸ (ty-subst-seq-fold σs (T [ σ ]))
                                       (ty-subst-comp T σ (fold σs))

tm-subst-seq-fold : (σs : Δ ⇒⁺ Γ) {T : Ty Γ} (t : Tm Γ T) →
                    t ⟦ σs ⟧' ≅ᵗᵐ ι[ ty-subst-seq-fold σs T ] (t [ fold σs ]')
tm-subst-seq-fold (σ ◼) t = symᵗᵐ ι-refl
tm-subst-seq-fold {Δ = Δ}{Γ} (σ ∷ σs) {T} t =
  begin
    (t [ σ ]') ⟦ σs ⟧'
  ≅⟨ tm-subst-seq-fold σs (t [ σ ]') ⟩
    ι[ ty-subst-seq-fold σs (T [ σ ]) ] ((t [ σ ]') [ fold σs ]')
  ≅⟨ ι-cong (tm-subst-comp t σ (fold σs)) ⟩
    ι[ ty-subst-seq-fold σs (T [ σ ]) ] (ι[ ty-subst-comp T σ (fold σs) ] (t [ σ ⊚ fold σs ]'))
  ≅˘⟨ ι-trans ⟩
    ι[ transᵗʸ (ty-subst-seq-fold σs (T [ σ ])) (ty-subst-comp T σ (fold σs)) ] (t [ σ ⊚ fold σs ]') ∎
  where open ≅ᵗᵐ-Reasoning

ty-subst-seq-cong : (σs τs : Δ ⇒⁺ Γ) (T : Ty Γ) →
                    fold σs ≅ˢ fold τs →
                    T ⟦ σs ⟧ ≅ᵗʸ T ⟦ τs ⟧
ty-subst-seq-cong σs τs T e =
  begin
    T ⟦ σs ⟧
  ≅⟨ ty-subst-seq-fold σs T ⟩
    T [ fold σs ]
  ≅⟨ ty-subst-cong-subst e T ⟩
    T [ fold τs ]
  ≅˘⟨ ty-subst-seq-fold τs T ⟩
    T ⟦ τs ⟧ ∎
  where open ≅ᵗʸ-Reasoning

tm-subst-seq-cong : (σs τs : Δ ⇒⁺ Γ) (t : Tm Γ T) →
                    (e : fold σs ≅ˢ fold τs) →
                    t ⟦ σs ⟧' ≅ᵗᵐ ι[ ty-subst-seq-cong σs τs T e ] (t ⟦ τs ⟧')
tm-subst-seq-cong {Δ = Δ} {T = T} σs τs t e =
  begin
    t ⟦ σs ⟧'
  ≅⟨ tm-subst-seq-fold σs t ⟩
    ι[ ty-subst-seq-fold σs T ] (t [ fold σs ]')
  ≅⟨ ι-cong (tm-subst-cong-subst t e) ⟩
    ι[ ty-subst-seq-fold σs T ] (ι[ ty-subst-cong-subst e T ] (t [ fold τs ]'))
  ≅˘⟨ ι-cong (ι-cong ι-symˡ) ⟩
    ι[ ty-subst-seq-fold σs T ] (ι[ ty-subst-cong-subst e T ] (ι[ symᵗʸ (ty-subst-seq-fold τs T) ] (ι[ ty-subst-seq-fold τs T ] (t [ fold τs ]'))))
  ≅˘⟨ ι-cong (ι-cong (ι-cong (tm-subst-seq-fold τs t))) ⟩
    ι[ ty-subst-seq-fold σs T ] (ι[ ty-subst-cong-subst e T ] (ι[ symᵗʸ (ty-subst-seq-fold τs T) ] (t ⟦ τs ⟧')))
  ≅˘⟨ ι-cong (ι-cong (ι-cong ι-refl)) ⟩
    ι[ ty-subst-seq-fold σs T ] (ι[ ty-subst-cong-subst e T ] (ι[ symᵗʸ (ty-subst-seq-fold τs T) ] (ι[ reflᵗʸ ] (t ⟦ τs ⟧'))))
  ≅˘⟨ ι-cong (ι-cong ι-trans) ⟩
    ι[ ty-subst-seq-fold σs T ] (ι[ ty-subst-cong-subst e T ] (ι[ transᵗʸ (symᵗʸ (ty-subst-seq-fold τs T)) reflᵗʸ ] (t ⟦ τs ⟧')))
  ≅˘⟨ ι-cong ι-trans ⟩
    ι[ ty-subst-seq-fold σs T ] (ι[ transᵗʸ (ty-subst-cong-subst e T) (transᵗʸ (symᵗʸ (ty-subst-seq-fold τs T)) reflᵗʸ) ] (t ⟦ τs ⟧'))
  ≅˘⟨ ι-trans ⟩
    ι[ transᵗʸ (ty-subst-seq-fold σs T) (transᵗʸ (ty-subst-cong-subst e T) (transᵗʸ (symᵗʸ (ty-subst-seq-fold τs T)) reflᵗʸ)) ] (t ⟦ τs ⟧')
  ≅⟨⟩
    ι[ ty-subst-seq-cong σs τs T e ] (t ⟦ τs ⟧') ∎
  where open ≅ᵗᵐ-Reasoning

ty-subst-seq-id : (σs : Γ ⇒⁺ Γ) (T : Ty Γ) →
                  fold σs ≅ˢ id-subst Γ →
                  T ⟦ σs ⟧ ≅ᵗʸ T
ty-subst-seq-id σs T e = transᵗʸ (ty-subst-seq-cong σs (id-subst _ ◼) T e)
                                 (ty-subst-id T)
