/-
# The `@[kb]` citation attribute

Every headline statement of the knowledge base is tagged with where it comes from:

    @[kb "washington1997" "Theorem 4.2"]
    theorem foo : ... := ...

The first string is a source key of `references.bib`, the second an optional locator inside that
source. Status (proved / stated) is *not* recorded here: it is derived from the kernel (the axioms
of the proof term), so the tag can never claim more than Lean has checked.

This is a local copy of the attribute of LeanKB (`LeanKB/Attr.lean` of
the author's knowledge-base template), same syntax and same data. NTKB does not depend on
LeanKB because LeanKB is pinned to Lean `v4.35.0` while NTKB follows the Mathlib commit of Tau Ceti
(Lean `v4.36.0-rc2`). When the toolchains agree, this file can be replaced by `import LeanKB`
(the namespace differs: `NTKB.kbEntries` here, `LeanKB.kbEntries` there).
-/
import Lean

namespace NTKB

open Lean

/-- One registry entry: a declaration plus its literature citation. -/
structure KBTag where
  decl : Name
  source : String
  locator : String
  deriving Inhabited, Repr

initialize kbExt : SimplePersistentEnvExtension KBTag (Array KBTag) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun arrs => arrs.foldl (· ++ ·) #[]
  }

/-- `@[kb "source" "locator"]` records a literature citation for the registry. -/
syntax (name := kbAttr) "kb " str (ppSpace str)? : attr

initialize registerBuiltinAttribute {
  name := `kbAttr
  descr := "Tag a declaration with a literature citation for the knowledge-base registry"
  applicationTime := .afterTypeChecking
  add := fun decl stx kind => do
    unless kind == AttributeKind.global do
      throwError "the kb attribute must be global"
    match stx with
    | `(attr| kb $src:str $[$loc:str]?) =>
      modifyEnv fun env => kbExt.addEntry env
        { decl, source := src.getString, locator := (loc.map (·.getString)).getD "" }
    | _ => Elab.throwUnsupportedSyntax
}

/-- All tagged declarations visible in `env` (imported and local). -/
def kbEntries (env : Environment) : Array KBTag :=
  kbExt.getState env

end NTKB
