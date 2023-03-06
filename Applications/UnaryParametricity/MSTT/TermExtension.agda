--------------------------------------------------
-- Specification of new term constructors for unary parametricity
--------------------------------------------------

open import Applications.UnaryParametricity.MSTT.TypeExtension.PredExtension

module Applications.UnaryParametricity.MSTT.TermExtension (pred-ext : PredExt) where

open import Data.List

open import Model.CwF-Structure as M
import Model.Type.Function as M
open import Applications.UnaryParametricity.Model as M using (_⟨→⟩_)

open import Applications.UnaryParametricity.MSTT.ModeTheory
open import Applications.UnaryParametricity.MSTT.TypeExtension pred-ext
open import MSTT.Parameter.TermExtension unary-par-mode-theory par-ty-ext

open import MSTT.TCMonad
open import MSTT.TypeChecker.ResultType unary-par-mode-theory par-ty-ext
open import Applications.UnaryParametricity.MSTT.Syntax.Type
open import MSTT.InterpretTypes unary-par-mode-theory par-ty-ext

open PredExt pred-ext

private variable
  m : ModeExpr
  margs : List ModeExpr

data ParTmCode : List ModeExpr → ModeExpr → Set where
  from-pred-code : (c : PredCode) (a : CodeLeft c) →
                  CodeRelation c a → ParTmCode [] ¶
  from-pred1-code : (c1 c2 : PredCode)
                   (f : CodeLeft c1 → CodeLeft c2) →
                   (CodeRelation c1 ⟨→⟩ CodeRelation c2) f →
                   ParTmCode [] ¶
  from-pred2-code : (c1 c2 c3 : PredCode)
                   (f : CodeLeft c1 → CodeLeft c2 → CodeLeft c3) →
                   (CodeRelation c1 ⟨→⟩ CodeRelation c2 ⟨→⟩ CodeRelation c3) f →
                   ParTmCode [] ¶
 
infer-interpret-par-code : ParTmCode margs m → InferInterpretExt margs m
  -- `margs` = []; `m` = ¶
infer-interpret-par-code (from-pred-code c a p) = λ Γ → return (FromPred c , M.from-pred a p)
infer-interpret-par-code (from-pred1-code c1 c2 f p) = λ Γ →
  return (FromPred c1 ⇛ FromPred c2 , M.lam _ (ι[ closed-natural (⟦⟧ty-natural (FromPred c2)) π ] M.from-pred1 f p))
infer-interpret-par-code (from-pred2-code c1 c2 c3 f p) = λ Γ → return
  (FromPred c1 ⇛ FromPred c2 ⇛ FromPred c3
  , M.lam _ (ι[ closed-natural (⟦⟧ty-natural (FromPred c2 ⇛ FromPred c3)) π ]
      M.lam _ (ι[ closed-natural (⟦⟧ty-natural (FromPred c3)) π ]
        M.from-pred2 f p)))

par-tm-ext : TmExt
TmExt.TmExtCode par-tm-ext = ParTmCode
TmExt.infer-interpret-code par-tm-ext = infer-interpret-par-code
