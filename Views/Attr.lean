import Views.Gen
import Views.View
import Views.Rel

namespace Lean.Views

initialize viewExtension : SimpleScopedEnvExtension WFViewType (RBMap Name WFViewType Name.cmp) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun map view => map.insert view.ind view
    initial := {}
  }

@[inline] def getWFViewType (ind : Name) : MetaM WFViewType := do
  let viewState := viewExtension.getState (← getEnv)
  let some view := viewState.find? ind | failure
  return view

initialize registerBuiltinAttribute {
  name := `view
  descr := "Marks an inductive type with the view attribute and generates associated types"
  add := fun indName stx _ => do
    let `(attr|view) := stx | throwError "unexpected @[view] attribute {stx}"
    match ← resolveGlobalName indName with
    | [] => throwError "unknown name {indName}"
    | _::_::_ => throwError "ambiguous name {indName}"
    | [(name,_)] => Meta.MetaM.run' do
      let ind ← getConstInfoInduct name <|> throwError "expected inductive type"
      let ⟨_, genName⟩ ← addGen ind
      let gen ← getConstInfoInduct genName
      let view ← addView ind gen
      let vinfo ← getConstInfoInduct view.view
      let rel ← addRel ind gen vinfo
      viewExtension.add rel
}
