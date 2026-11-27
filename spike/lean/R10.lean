/-
R-10 (PLAN stage 1): Lean TPE (cedar-spec #1015) residuals of the five KEP-style policies, printed by
a type-erased, association-normalised printer in the same grammar as `spike::audit::canon` (Rust,
over `Policy::to_json`). Regenerate the golden file with:
  cd lean && lake env lean ../spike/lean/R10.lean > ../spike/lean/R10.out
The Rust test `r10_lean_and_rust_residuals_agree` compares R10.out with the Rust output.
-/
import Cedar.TPE
import Cedar.Spec
import Cedar.Validation
open Cedar.Spec Cedar.TPE Cedar.Validation Cedar.Data

def ActionT : EntityType := ⟨"Action", []⟩
def UserT : EntityType := ⟨"User", []⟩
def ResT : EntityType := ⟨"Res", []⟩

def metaTy : CedarType := .record (Map.make [
  ("name", .optional .string),
  ("labels", .optional (.record (Map.make [("owner", .optional .string)]))),
  ("finalizers", .optional (.set .string))])
def objTy : CedarType := .record (Map.make [
  ("metadata", .optional metaTy),
  ("spec", .optional (.record (Map.make [("nodeName", .optional .string), ("replicas", .optional .int)])))])

def schema : Schema :=
  ⟨Map.make [
    (ActionT, .standard ⟨default, default, default⟩),
    (UserT, .standard ⟨default, Map.make [("name", .required .string), ("nodeName", .required .string)], default⟩),
    (ResT, .standard ⟨default, Map.make [("name", .optional .string), ("request", .optional objTy), ("stored", .optional objTy)], default⟩)],
   Map.make [(⟨ActionT, "Create"⟩, ⟨Set.singleton UserT, Set.singleton ResT, default, default⟩),
             (⟨ActionT, "Update"⟩, ⟨Set.singleton UserT, Set.singleton ResT, default, default⟩)]⟩

-- expression helpers
def res : Expr := .var .resource
def dot (e : Expr) (a : String) : Expr := .getAttr e a
def path (xs : List String) : Expr := xs.foldl dot res
def hasA (e : Expr) (a : String) : Expr := .hasAttr e a
-- left-nested, like the Cedar text parser used on the Rust side (association matters for the
-- short-circuit simplifications of TPE: `(A && false) && error` does not fold, `A && (false && error)` does)
def conj : List Expr → Expr
  | [] => .lit (.bool true)
  | e :: es => es.foldl (fun acc x => .and acc x) e
def sloc (s : String) : Expr := .lit (.string s)
def princ (a : String) : Expr := .getAttr (.var .principal) a

def pOwner : Policy := ⟨"owner", .permit, .principalScope .any,
  .actionInAny [⟨ActionT, "Create"⟩, ⟨ActionT, "Update"⟩], .resourceScope .any,
  [⟨.when, conj [hasA res "request", hasA (path ["request"]) "metadata", hasA (path ["request", "metadata"]) "labels",
                 hasA (path ["request", "metadata", "labels"]) "owner",
                 .binaryApp .eq (path ["request", "metadata", "labels", "owner"]) (princ "name")]⟩]⟩
def pUnchanged : Policy := ⟨"unchanged", .forbid, .principalScope .any, .actionScope (.eq ⟨ActionT, "Update"⟩), .resourceScope .any,
  [⟨.when, conj [hasA res "stored", hasA (path ["stored"]) "spec", hasA (path ["stored", "spec"]) "nodeName",
                 hasA res "request", hasA (path ["request"]) "spec", hasA (path ["request", "spec"]) "nodeName",
                 .unaryApp .not (.binaryApp .eq (path ["stored", "spec", "nodeName"]) (path ["request", "spec", "nodeName"]))]⟩]⟩
def pPrefix : Policy := ⟨"prefix", .permit, .principalScope .any, .actionScope (.eq ⟨ActionT, "Create"⟩), .resourceScope .any,
  [⟨.when, conj [hasA res "name",
                 .unaryApp (.like [.justChar 's', .justChar 'a', .justChar 'f', .justChar 'e', .justChar '-', .star]) (path ["name"])]⟩]⟩
def pFinalizer : Policy := ⟨"finalizer", .forbid, .principalScope .any, .actionScope .any, .resourceScope .any,
  [⟨.when, conj [hasA res "request", hasA (path ["request"]) "metadata", hasA (path ["request", "metadata"]) "finalizers",
                 .binaryApp .contains (path ["request", "metadata", "finalizers"]) (sloc "protected")]⟩]⟩
def pNodeBound : Policy := ⟨"nodebound", .permit, .principalScope .any, .actionScope (.eq ⟨ActionT, "Update"⟩), .resourceScope .any,
  [⟨.when, conj [hasA res "stored", hasA (path ["stored"]) "spec", hasA (path ["stored", "spec"]) "nodeName",
                 .binaryApp .eq (path ["stored", "spec", "nodeName"]) (princ "nodeName")]⟩]⟩

def policies : List Policy := [pOwner, pUnchanged, pPrefix, pFinalizer, pNodeBound]

def alice : EntityUID := ⟨UserT, "alice"⟩
def r1 : EntityUID := ⟨ResT, "r1"⟩
def preq (act : String) : PartialRequest :=
  { principal := ⟨UserT, some "alice"⟩, action := ⟨ActionT, act⟩, resource := ⟨ResT, some "r1"⟩, context := some Map.empty }
def aliceData : PartialEntityData := ⟨some (Map.make [("name", .value (.prim (.string "alice"))), ("nodeName", .value (.prim (.string "n1")))]), some Set.empty, some Map.empty⟩
def mkRes (attrs : List (String × AttrState)) : PartialEntityData := ⟨some (Map.make attrs), some Set.empty, some Map.empty⟩
def ents (r : PartialEntityData) : PartialEntities := Map.make [(alice, aliceData), (r1, r)]
def vs (s : String) : AttrState := .value (.prim (.string s))

-- printer: same grammar as spike::audit::canon
mutual
partial def canonVal : Value → String
  | .prim (.bool b) => toString b
  | .prim (.int i) => toString i
  | .prim (.string x) => "\"" ++ x ++ "\""
  | .prim (.entityUID u) => u.ty.id ++ "::\"" ++ u.eid ++ "\""
  | .set s => "(set " ++ " ".intercalate (s.elts.map canonVal) ++ ")"
  | .record _ => "?record"
  | .ext _ => "?ext"
partial def flat (isAnd : Bool) : Residual → List String
  | e@(.and a b _) => if isAnd then flat isAnd a ++ flat isAnd b else [canon e]
  | e@(.or a b _) => if isAnd then [canon e] else flat isAnd a ++ flat isAnd b
  | e => [canon e]
partial def canon : Residual → String
  | .val v _ => canonVal v
  | .var v _ => match v with | .principal => "principal" | .resource => "resource" | .action => "action" | .context => "context"
  | .ite c t e _ => "(if " ++ canon c ++ " " ++ canon t ++ " " ++ canon e ++ ")"
  | .and a b _ => "(and " ++ " ".intercalate (flat true a ++ flat true b) ++ ")"
  | .or a b _ => "(or " ++ " ".intercalate (flat false a ++ flat false b) ++ ")"
  | .unaryApp .not e _ => "(! " ++ canon e ++ ")"
  | .unaryApp (.like p) e _ =>
      "(like " ++ canon e ++ " \"" ++ String.join (p.map fun x => match x with | .star => "*" | .justChar c => c.toString) ++ "\")"
  | .unaryApp _ e _ => "(?unary " ++ canon e ++ ")"
  | .binaryApp op a b _ =>
      let o := match op with
        | .eq => "==" | .mem => "in" | .contains => "contains" | .containsAny => "containsAny"
        | .less => "<" | .lessEq => "<=" | .add => "+" | .sub => "-" | .mul => "*" | _ => "?binop"
      "(" ++ o ++ " " ++ canon a ++ " " ++ canon b ++ ")"
  | .getAttr e a _ => "(. " ++ canon e ++ " " ++ a ++ ")"
  | .hasAttr e a _ => "(has " ++ canon e ++ " " ++ a ++ ")"
  | .extHasAttr _ _ _ _ => "?extHas"
  | .set ls _ => "(set " ++ " ".intercalate (ls.map canon) ++ ")"
  | .record _ _ => "?record"
  | .call _ _ _ => "?call"
  | .error _ => "error"
end

def scenarios : List (String × String × PartialEntityData) := [
  ("create", "Create", mkRes [("name", .unknown), ("request", .present), ("stored", .absent)]),
  ("update", "Update", mkRes [("name", vs "settings"), ("request", .present), ("stored", .unknown)]),
  ("update-partial", "Update", mkRes [("name", vs "settings"),
      ("request", .partialRecord (Map.make [("metadata", .present), ("spec", .partialRecord (Map.make [("nodeName", .present)]))])),
      ("stored", .partialRecord (Map.make [("metadata", .unknown),
          ("spec", .partialRecord (Map.make [("nodeName", vs "n1"), ("replicas", .unknown)]))]))]),
  ("delete-like", "Update", mkRes [("name", vs "settings"), ("request", .absent), ("stored", .present)])]

#eval do
  for (sn, act, r) in scenarios do
    for p in policies do
      match evaluatePolicy schema p (preq act) (ents r) with
      | .ok x => IO.println s!"{sn}|{p.id}|{canon x}"
      | .error e => IO.println s!"{sn}|{p.id}|LEAN-ERROR {(toString (repr e)).take 100}"
