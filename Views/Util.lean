import Lean.Meta.Constructions
import Batteries

namespace Lean
open Meta

def mkNewLevelName (u : Name := `u) (ls : List Name) : Name :=
  bif ls.contains u then loop 0 ls.length else u
where
  loop
    | i, fuel+1 =>
      let u := u.appendIndexAfter i
      bif ls.contains u then loop (i+1) fuel else u
    | _, 0 => unreachable!

def mkToName (name : Name) : Name := .mkStr1 ("to" ++ name.getString!)

def Meta.mkOutParam (expr : Expr) : MetaM Expr := do
  let u ← getLevel expr
  return mkApp (mkConst `outParam [u]) expr

structure StructureVal extends ConstantVal where
  ctor : Name
  fields : List Name
  numParams : Nat
  isUnsafe : Bool
  isClass : Bool
  deriving Inhabited

def StructureVal.projs : StructureVal → List Name
  | {name := name, fields := fields, ..} => fields.map (name ++ .)

def StructureVal.toInductiveVal : StructureVal → InductiveVal
  | {toConstantVal, ctor, numParams, isUnsafe, ..} => {
      toConstantVal with
      numParams := numParams
      numIndices := 0
      all := [toConstantVal.name]
      ctors := [ctor]
      isUnsafe := isUnsafe
      isRec := false
      isNested := false
      isReflexive := false
    }

def mkSimpleInductiveDecl (ind : InductiveVal) (ctors : List ConstructorVal) : Declaration :=
  .inductDecl ind.levelParams ind.numParams [mkType] ind.isUnsafe
where
  mkType : InductiveType := {
    name := ind.name
    type := ind.type
    ctors := ctors.map mkCtor
  }
  mkCtor ctor : Constructor := {
    name := ctor.name
    type := ctor.type
  }

def addSimpleInductive (ind : InductiveVal) (ctors : List ConstructorVal) : MetaM Unit := do
  addDecl (mkSimpleInductiveDecl ind ctors)
  mkRecOn ind.name
  mkCasesOn ind.name
  mkNoConfusion ind.name
  mkBelow ind.name
  mkIBelow ind.name
  mkBRecOn ind.name
  mkBInductionOn ind.name

@[extern "lean_mk_projections"]
private opaque mkProjections (env : Environment) (structName : Name) (projs : List Name) (isClass : Bool) : Except KernelException Environment

def addProjections (struct : Name) (projs : List Name) (isClass : Bool) : MetaM Unit := do
  setEnv (← ofExceptKernelException <| mkProjections (← getEnv) struct projs isClass)

def mkSimpleDescr : StructureVal → StructureDescr
  | {name, fields, ..} => {
    structName := name
    fields := mkFields name fields.toArray
  }
where
  mkFields name fields := fields.map fun n => {
    fieldName := n
    projFn := name ++ n
    subobject? := none
    binderInfo := .default
  }

def addSimpleStructure (struct : StructureVal) (ctor : ConstructorVal) : MetaM Unit := do
  addSimpleInductive struct.toInductiveVal [ctor]
  addProjections struct.name struct.projs struct.isClass
  let mut env ← getEnv
  if struct.isClass then env ← ofExcept <| addClass env struct.name
  env := registerStructure env <| mkSimpleDescr struct
  setEnv env

initialize registerTraceClass `views
