/-
Copyright (c) 2025, 2026 Stefan Kusterer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import SemVer

open Version

def getVersion : IO Version := do

  let input ← (← IO.getStdin).getLine
  let version ← (parse input.trimAscii.toString).toIO!
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

    if version_0 = version_1 then
      IO.println "both versions are equal"

    if version_0 < version_1 then
      IO.println s!"the first version comes before the second, i.e. {version_0} < {version_1}"
    else
      if version_1 < version_0 then
        IO.println s!"the second version comes before the first, i.e. {version_1} < {version_0}"
      else
        IO.println s!"the provided versions are *not* comparable with respect to the less-than-relation (<)"

  catch e =>
    IO.println e
