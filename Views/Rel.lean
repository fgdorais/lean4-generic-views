import Views.Util
import Views.Gen
import Views.View

open Lean Meta Elab

namespace Lean.Views

structure WFViewType extends ViewType where
  rel : Name
  deriving Inhabited

def mkRel (_ind gen view : InductiveVal) (relName : Name) : MetaM (InductiveVal × List ConstructorVal) := do
  let type ← relType
  let genCtors ← gen.ctors.mapM getConstInfoCtor
  let ctors ← genCtors.foldlM (fun a b => a.append <$> ctorVals a.length b) []
  return ({gen with
    name := relName
    type := type
    numParams := gen.numParams + 1
    numIndices := gen.numIndices * 2 + 2
    all := [relName]
    ctors := ctors.map fun ctor => ctor.name
  }, ctors)

where

  relType : MetaM Expr := forallTelescope gen.type fun ps _ => do
    let params := ps[:gen.numParams].toArray
    let indices := ps[gen.numParams:].toArray
    let pmap ← params.mapM fun p => do
      return (← p.fvarId!.getUserName, .implicit,
        fun es => do
          let t ← inferType p
          let t := t.replaceFVars params[:es.size] es
          return t)
    withLocalDecls pmap fun params => do
      let ω := params.back
      let viewType ← Meta.mkAppM view.name params
      let imap1 ← indices.mapM fun p => do
        return ((← p.fvarId!.getUserName).appendIndexAfter 1, .implicit,
          fun es => do
            let t ← inferType p
            let t := t.replaceFVars ps[:gen.numParams+es.size] (params ++ es)
            return t)
      let imap2 ← indices.mapM fun p => do
        return ((← p.fvarId!.getUserName).appendIndexAfter 2, .implicit,
          fun es => do
            let t ← inferType p
            let t := t.replaceFVars ps[:gen.numParams+es.size] (params ++ es)
            return t)
      withLocalDecls imap1 fun idx1 => withLocalDecls imap2 fun idx2 => do
      withLocalDeclD `a1 (mkAppN ω idx1) fun a1 => withLocalDeclD `a2 (mkAppN ω idx2) fun a2 => do
        let indices := (Array.zip idx1 idx2).foldl (fun | is, (i1, i2) => is.push i1 |>.push i2) #[]
        withLocalDecl `view .instImplicit viewType fun viewInst => do
          let params := params.push viewInst
          mkForallFVars (params ++ indices ++ #[a1, a2]) (mkSort 0)

  ctorVals (idx : Nat) (ctor : ConstructorVal) : MetaM (List ConstructorVal) := do
    forallTelescope ctor.type fun ps t => do
      let indices := t.getAppArgs[ctor.numParams:].toArray
      let levels := ctor.levelParams.map mkLevelParam
      let params := ps[:ctor.numParams].toArray
      let fields := ps[ctor.numParams:].toArray
      let ω := params.back
      withLocalDeclD `a (mkAppN ω indices) fun a => do
        let ctorExpr := mkConst ctor.name levels
        let ctorExpr := mkAppN ctorExpr (params ++ fields)
        let viewType := mkConst view.name levels
        let viewType := mkAppN viewType params
        withLocalDecl `view .instImplicit viewType fun viewInst => do
          let params := params.push viewInst
          let viewDest := mkConst (view.name ++ `dest) levels
          let viewDest := mkAppN viewDest (params ++ indices.push a)
          let mut acc := #[]
          for i in [:fields.size] do
            let t ← inferType fields[i]!
            if t.getAppFn == ω then
              let args := t.getAppArgs
              let relArgs := (args.zip indices).foldl (fun | is, (i1, i2) => is.push i1 |>.push i2) params
              let relArgs := relArgs.push fields[i]! |>.push a
              let relType := mkConst relName levels
              let relType := mkAppN relType relArgs
              let eqType ← mkEq ctorExpr viewDest
              acc := acc.push <| ← withLocalDeclD `h eqType fun eqExpr => do
                let ctorType ← mkForallFVars (params ++ fields ++ [a, eqExpr]) relType
                let ctorName := ctor.name.replacePrefix ctor.induct relName |>.appendIndexAfter i
                pure {ctor with
                  type := ctorType
                  name := ctorName
                  induct := relName
                  numParams := gen.numParams + 1
                  numFields := 1
                  cidx := idx + acc.size
                }
            else if t.getAppFn.getForallBody == ω then
              throwError "reflexive inductive types are not yet supported"
          return acc.toList

def defaultRelName (name : Name) := name ++ `Rel

def addRel (ind gen view : InductiveVal) (relName : Option Name := none) : MetaM WFViewType := do
  let relName := match relName with
    | some relName => relName
    | none => defaultRelName ind.name
  let (relInd, relCtors) ← mkRel ind gen view relName
  Lean.addSimpleInductive relInd relCtors
  return {ind := ind.name, gen := gen.name, view := view.name, rel := relName}
