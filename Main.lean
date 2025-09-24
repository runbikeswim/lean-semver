/-
Copyright (c) 2025 Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SemVer

open Version

def getVersion : IO Version := do

  let input ← (← IO.getStdin).getLine
  let version ← doParserResult (parse input.trim)
  return version

def main : IO Unit := do

  try
    IO.print "please enter the first version identifier --> "
    let version_0 ← getVersion

    IO.print "please enter the second version identifier -> "
    let version_1 ← getVersion

    IO.println "the term representing the first version identifier is:"
    IO.println ((repr version_0).pretty 128 0)

    IO.print "the public API related to the first version is "
    if version_0.isStable then
      IO.println "stable"
    else
      IO.println "*not* stable"

    IO.println "the term representing the second version identifier is:"
    IO.println ((repr version_1).pretty 128 0)

    IO.print "the public API related to the second version is "
    if version_1.isStable then
      IO.println "stable"
    else
      IO.println "*not* stable"

    IO.println "for the precedence of the first and second version, the following is true:"
    if version_0 < version_1 then
      IO.println s!"    {version_0} < {version_1}"
    else
      IO.println s!"  ¬ {version_0} < {version_1}"

  catch e =>
    IO.println e
