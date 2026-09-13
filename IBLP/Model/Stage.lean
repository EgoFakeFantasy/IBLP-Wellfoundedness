import IBLP.Model.Formula

namespace IBLP
open FullMarkedBLP

universe u

/-- 证明中实际构造的模型阶段。初始映射给出一阶背景理论的输送；
它不进入 Good 的有限证书，也不假定行图来自全域 owner。 -/
structure ModelStage where
  model : TransitiveClass.{u}
  fromUniverse : universeClass.toTransitiveClass.ElementaryMap model
  countablyClosed : model.CountablyClosed

def initialStage : ModelStage.{u} where
  model := universeClass.toTransitiveClass
  fromUniverse := FirstOrder.Language.ElementaryEmbedding.refl membershipLanguage _
  countablyClosed := universeClass_countablyClosed

def ModelStage.next (stage : ModelStage.{u}) (N : TransitiveClass.{u})
    (j : stage.model.ElementaryMap N) (closed : N.CountablyClosed) : ModelStage.{u} where
  model := N
  fromUniverse := j.comp stage.fromUniverse
  countablyClosed := closed

/-- 只在元层使用的实际逐公式输送，不向对象语言添加真谓词。 -/
theorem ModelStage.transfer_sentence (stage : ModelStage.{u}) (phi : membershipLanguage.Sentence) :
    phi.Realize universeClass.{u}.toTransitiveClass.Element ↔ phi.Realize stage.model.Element :=
  stage.fromUniverse.map_sentence phi

theorem ModelStage.transfer_closed (stage : ModelStage.{u}) (phi : RankPredicateFormula 0 0)
    (h : universeClass.{u}.toTransitiveClass.realize phi Fin.elim0) :
    stage.model.realize phi Fin.elim0 := by
  have he := stage.fromUniverse.realize_iff phi Fin.elim0
  have same : stage.fromUniverse ∘ Fin.elim0 = Fin.elim0 := by
    funext i
    exact Fin.elim0 i
  rw [same] at he
  exact he.mpr h

end IBLP
