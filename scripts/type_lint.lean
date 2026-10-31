/-
  Report-only driver for the type-doctrine linters
  (`docs/lean/type-doctrine.md` §3-4a). Prints one JSON line per finding,
  then one JSON summary line. Not part of the default build; build this
  module first with `lake build ArmadaLean.Lint.TypeDoctrine`, then run:

    lake env lean scripts/type_lint.lean
-/
import ArmadaLean
import ArmadaLean.Lint.TypeDoctrine

open Lean Meta ArmadaLean.Lint.TypeDoctrine

def jsonStr (s : String) : String :=
  let esc := s.foldl (init := "") fun acc c =>
    match c with
    | '"' => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | '\n' => acc ++ "\\n"
    | '\t' => acc ++ "\\t"
    | _ => acc.push c
  "\"" ++ esc ++ "\""

def jsonArr (xs : List String) : String :=
  "[" ++ String.intercalate "," xs ++ "]"

def report : MetaM Unit := do
  let env ← getEnv
  let data ← computeGlobalData
  let nitroCount := (data.decls.filter (·.isNitro)).size
  let poolCount := data.decls.size - nitroCount

  for (key, uses) in data.repeated do
    let names := (uses.map Prod.fst).toList.eraseDups.map (jsonStr ∘ toString)
    let exampleHyp := uses[0]!.2
    IO.println
      s!"\{\"linter\":\"repeatedPremise\",\"shape\":{jsonStr key},\"declarations\":{jsonArr names},\"example\":{jsonStr exampleHyp}}"

  for ((ty, field), shapes) in data.variant do
    let shapeStrs := shapes.toList.map fun (_, pretty, names) =>
      "{\"shape\":" ++ jsonStr pretty ++ ",\"declarations\":" ++
        jsonArr (names.toList.map (jsonStr ∘ toString)) ++ "}"
    IO.println
      s!"\{\"linter\":\"premiseVariant\",\"type\":{jsonStr (toString ty)},\"field\":{jsonStr (toString field)},\"variants\":{jsonArr shapeStrs}}"

  for (declName, fieldVar, pretty) in data.loose do
    IO.println
      s!"\{\"linter\":\"looseHypothesis\",\"declaration\":{jsonStr (toString declName)},\"var\":{jsonStr (toString fieldVar)},\"hypothesis\":{jsonStr pretty}}"

  for (declName, binderName, rhs) in data.alias do
    IO.println
      s!"\{\"linter\":\"aliasHypothesis\",\"declaration\":{jsonStr (toString declName)},\"binder\":{jsonStr (toString binderName)},\"rhs\":{jsonStr rhs}}"

  for (declName, isNitro, hit) in data.layer do
    let layer := if isNitro then "nitro" else "pool"
    IO.println
      s!"\{\"linter\":\"layerDiscipline\",\"declaration\":{jsonStr (toString declName)},\"layer\":{jsonStr layer},\"baseOps\":{jsonArr (hit.toList.map (jsonStr ∘ toString))}}"

  -- Spec-level totals (the §4a denominator), recomputed here from the
  -- same `scopedTheoremNames`/citation predicates the linter module
  -- exposes (layerDiscipline's scope is theorems, not every declaration).
  let names := scopedTheoremNames env
  let mut specNitro := 0
  let mut specPool := 0
  for n in names do
    if let some doc ← findDocString? env n then
      if isNitroModule env n then
        if nitroCitation doc then specNitro := specNitro + 1
      else
        if poolCitation doc then specPool := specPool + 1

  let layerNitroHits := (data.layer.filter (·.2.1)).size
  let layerPoolHits := data.layer.size - layerNitroHits

  IO.println
    s!"\{\"summary\":true,\"decls_scanned\":{data.decls.size},\"nitro_decls\":{nitroCount},\"pool_decls\":{poolCount},\"repeatedPremise_groups\":{data.repeated.size},\"premiseVariant_groups\":{data.variant.size},\"looseHypothesis_findings\":{data.loose.size},\"aliasHypothesis_findings\":{data.alias.size},\"layerDiscipline_nitro_spec_total\":{specNitro},\"layerDiscipline_nitro_hits\":{layerNitroHits},\"layerDiscipline_pool_spec_total\":{specPool},\"layerDiscipline_pool_hits\":{layerPoolHits}}"

#eval report
