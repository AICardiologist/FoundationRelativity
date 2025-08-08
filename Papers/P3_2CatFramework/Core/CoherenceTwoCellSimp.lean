/-
  Simp lemmas for Papers.P3.TwoCell.
  Split into a companion file to keep Core/Coherence.lean slim and to avoid
  accidental namespace/placement issues.
-/
import Papers.P3_2CatFramework.Core.Coherence

namespace Papers.P3
namespace TwoCell

-- With app : φ.map_obj x = ψ.map_obj x, composition is α ▸ β = α.trans β

@[simp] theorem vcomp_app {F G} {φ ψ χ : Interp F G}
    (α : TwoCell φ ψ) (β : TwoCell ψ χ) (x : F.U) :
    (TwoCell.vcomp α β).app x = (α.app x).trans (β.app x) := rfl

@[simp] theorem id_app {F G} (φ : Interp F G) (x : F.U) :
    (TwoCell.id φ).app x = rfl := rfl

@[simp] theorem lwhisker_app {E F G} {φ ψ : Interp F G}
    (η : Interp E F) (α : TwoCell φ ψ) (x : E.U) :
    (TwoCell.lwhisker η α).app x =
      (by simpa [Interp.vcomp] using α.app (η.map_obj x)) := rfl

@[simp] theorem rwhisker_app {F G H} {φ ψ : Interp F G}
    (α : TwoCell φ ψ) (η : Interp G H) (x : F.U) :
    (TwoCell.rwhisker α η).app x =
      (by simpa [Interp.vcomp] using congrArg η.map_obj (α.app x)) := rfl

end TwoCell
end Papers.P3