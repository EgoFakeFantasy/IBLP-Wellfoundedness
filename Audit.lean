import IBLP
import Lean

open Lean Elab Command in
run_elab do
  let env ← getEnv
  let permitted : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut constants := 0
  let mut theorems := 0
  let mut privateConstants := 0
  let mut used : Array Name := #[]
  for (name, info) in env.constants.toList do
    if (`IBLP).isPrefixOf (privateToUserName name) then
      constants := constants + 1
      if name != privateToUserName name then
        privateConstants := privateConstants + 1
      if info.isTheorem then
        theorems := theorems + 1
      let axioms ← collectAxioms name
      for ax in axioms do
        unless permitted.contains ax do
          throwError "Unexpected axiom {ax} in {name}"
        unless used.contains ax do
          used := used.push ax
  logInfo m!"Kernel audit passed: {constants} IBLP constants (including {privateConstants} private constants); {theorems} theorem constants; axioms: {used}"
