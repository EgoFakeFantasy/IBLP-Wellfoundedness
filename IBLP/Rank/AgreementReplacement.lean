import IBLP.Rank.WeakAgreement

namespace IBLP.CutAction
universe u v
variable {S : Type v} {C : CutSpace.{u} S} {F U V W : CutAction C}

theorem AllInputAgreement.replace_word (old : AllInputAgreement F V V.bound)
    (replacement : AllInputAgreement V W W.bound) (bound : W.bound ≤ V.bound) :
    AllInputAgreement F W W.bound := fun z => ((old.shrink bound) z).trans (replacement z)

theorem AllInputAgreement.replace_inner (old : AllInputAgreement F (U.comp V) (U.comp V).bound)
    (replacement : AllInputAgreement V W W.bound) (bound : W.bound ≤ V.bound) :
    AllInputAgreement F (U.comp W) (U.comp W).bound :=
  old.replace_word (replacement.comp_left U) (U.monotone bound)

end IBLP.CutAction
