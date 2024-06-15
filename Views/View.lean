import Views.Util
import Views.Gen

open Lean Meta Elab

namespace Lean.Views

structure ViewType extends GenType where
  view : Name
  deriving Inhabited

def mkView (gen : InductiveVal) (viewName : Name) : MetaM (StructureVal × ConstructorVal) := do
  let type ← viewType
  trace[views] "view type {viewName} : {type}"
  let struct := {gen with
    name := viewName
    ctor := ctorName
    type := type
    isClass := true
    fields := [`dest]
  }
  let type ← ctorType
  trace[views] "view ctor {ctorName} : {type}"
  let ctor := {gen with
    name := ctorName
    type := ← ctorType
    cidx := 0
    numFields := 1
    induct := viewName
  }
  return (struct, ctor)
where
  viewType := forallTelescope gen.type fun ps val => do
    let params := ps[:gen.numParams].toArray
    withLocalDecls (← params.mapM fun p => do
      let binder ← p.fvarId!.getBinderInfo
      return (← p.fvarId!.getUserName, binder,
        fun es => do
          let t ← inferType p
          let t := t.replaceFVars params[:es.size] es
          bif binder == .default && es.size < params.size - 1 then
            mkOutParam t
          else
            return t)
    ) fun params => mkForallFVars params val
  ctorName := viewName ++ `mk
  ctorType := forallTelescope gen.type fun ps _ => do
    let params := ps[:gen.numParams].toArray
    let genVal ← mkConstWithLevelParams gen.name
    let levels := genVal.constLevels!
    let pmap ← params.mapM fun p => do
      return (← p.fvarId!.getUserName, .implicit,
        fun es => do
          let t ← inferType p
          let t := t.replaceFVars ps[:es.size] es
          return t)
    withLocalDecls pmap fun ps => do
      let params := ps[:gen.numParams].toArray
      let ω := params.back
      forallTelescope (← inferType ω) fun indices _ => do
        let dest := Expr.forallE `h (mkAppN ω indices) (mkAppN genVal (params ++ indices)) .default
        let dest ← mkForallFVars indices dest
        let type := mkAppN (.const viewName levels) params
        let type := Expr.forallE `dest dest type .default
        mkForallFVars params type

def defaultViewName (name : Name) := name ++ `View

def addView (ind gen : InductiveVal) (viewName : Option Name := none) : MetaM ViewType := do
  let viewName := match viewName with
    | some viewName => viewName
    | none => defaultViewName ind.name
  let (viewStruct, viewCtor) ← mkView gen viewName
  Lean.addSimpleStructure viewStruct viewCtor
  return {ind := ind.name, gen := gen.name, view := viewName}
