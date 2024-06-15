import Views.Util

open Lean Meta Elab

namespace Lean.Views

structure GenType where
  ind : Name
  gen : Name
  deriving Inhabited

def mkGenInd (ind : InductiveVal) (genName : Name) : MetaM InductiveVal := do
  let type ← genType
  trace[views] "gen type {genName} : {type}"
  return {ind with
    name := genName
    type := type
    numParams := ind.numParams + 1
    levelParams := newLevel :: ind.levelParams
    ctors := ind.ctors.map (Name.replacePrefix · ind.name genName)
    all := [genName]
    isRec := false
  }
where
  newLevel := mkNewLevelName `w ind.levelParams
  genType := do
    forallTelescope ind.type fun ps v => do
      let indices := ps[ind.numParams:].toArray
      let params := ps[:ind.numParams].toArray
      let w := mkLevelParam newLevel
      let l := (Level.imax w v.sortLevel!).normalize
      withLocalDecl `ω .default (← mkForallFVars indices (mkSort w)) fun ω => do
        mkForallFVars (params.push ω ++ indices) (mkSort l)

def mkGenCtor (gen : InductiveVal) (ctor : ConstructorVal) : MetaM ConstructorVal := do
  let type ← ctorType
  trace[views] "gen ctor type {ctorName} : {type}"
  return {ctor with
    name := ctorName
    levelParams := gen.levelParams
    numParams := ctor.numParams + 1
    induct := gen.name
    type := type
  }
where
  ctorName := ctor.name.replacePrefix ctor.induct gen.name
  ctorType := do
    forallTelescope ctor.type fun ps val => do
      let params := ps[:ctor.numParams].toArray
      let fields := ps[ctor.numParams:].toArray
      let indices := val.getAppArgs[ctor.numParams:].toArray
      let levels := val.getAppFn.constLevels!
      let .forallE n t _ _ ← instantiateForall gen.type params | failure
      withLocalDecl n .implicit t fun ω => do
        let params := params ++ #[ω]
        let levels := t.getForallBody.sortLevel! :: levels
        withLocalDecls (← fields.mapM fun f => do
          return (← f.fvarId!.getUserName, ← f.fvarId!.getBinderInfo,
            fun es => do
              let t ← forallTelescope (← inferType f) fun ps t =>
                let t :=
                  if t.isAppOf ctor.induct then
                    mkAppN ω t.getAppArgs[ctor.numParams:]
                  else t
                mkForallFVars ps t
              return t.replaceFVars fields[:es.size] es)
        ) fun ps => do
          let indices := indices.map fun i => i.replaceFVars fields ps
          let fields := ps[:ctor.numFields].toArray
          let val := .const gen.name levels
          let val := mkAppN val (params ++ indices)
          mkForallFVars (params ++ fields) val

def defaultGenName (name : Name) : Name := name ++ `Gen

def addGen (ind : InductiveVal) (genName : Option Name := none) : MetaM GenType := do
  if ind.all.length != 1 ∨ ind.isNested then
    throwError "mutual and nested inductive types are not supported"
  let genName := match genName with
    | some genName => genName
    | none => defaultGenName ind.name
  let genInd ← mkGenInd ind genName
  let genCtors ← ind.ctors.mapM fun ctor => do mkGenCtor genInd (← getConstInfoCtor ctor)
  Lean.addSimpleInductive genInd genCtors
  return ⟨ind.name, genInd.name⟩
