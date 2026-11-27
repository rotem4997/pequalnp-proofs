# Contributing a proof

One pull request proves one posted gap. The rules below are checked by a program. A pull
request that breaks one of them is refused, and the reason is the only reply.

## The pull request

1. It adds exactly one file and changes nothing else. No edits, no deletions, no renames, no
   second file.
2. The file is the one the desk named for your gap. Its path has the form
   `lean/PEqualNP/Outside/L_<gap>.lean`, with lower case letters, digits and underscores only.
3. It is a plain text file in UTF-8, at most 512 KiB. Not a link, not executable.
4. The gap must still be posted when the pull request is checked. If someone else's proof of
   the same gap was accepted earlier, the gap is closed.

## The file

1. Imports come at the top, one per line, in the plain form `import Some.Module`, with nothing
   else among them (no comments between or before them, no `public`, `meta` or `module`).
2. It may import only `Mathlib`, modules of Mathlib, and the project modules listed for the
   gap. Nothing else.
3. After the import lines, the word `import` may not appear anywhere in the file, comments
   included.
4. It declares one theorem, named after the module. For `lean/PEqualNP/Outside/L_gct_101.lean`
   that is `PEqualNP.Outside.L_gct_101`.
5. The theorem proves exactly the posted statement. A stronger, weaker or reworded statement is
   refused. If you think the statement is false or needs another hypothesis, do not change it:
   release the gap at the desk with `statement_seems_false` or `hypothesis_too_weak`.
6. No `sorry`. No axioms beyond `propext`, `Classical.choice`, `Quot.sound`. No
   `native_decide`.
7. Helper lemmas and helper definitions go inside the same file, inside one namespace block
   named after the module: `namespace PEqualNP.Outside.L_gct_101` ... `end
   PEqualNP.Outside.L_gct_101` (or `..._aux`, or a name below either). Outside that block stand
   only the imports, `open` lines, the four limit options, comments and the one theorem, written
   with its full name and last in the file. `namespace`, `section` and `end` start at column 0,
   and each `end` names what it closes. Helpers should not be instances or simp lemmas: those
   travel to every file that imports yours. For example:

       import Mathlib

       namespace PEqualNP.Outside.L_gct_101
       lemma helper : 1 + 1 = 2 := rfl
       end PEqualNP.Outside.L_gct_101

       theorem PEqualNP.Outside.L_gct_101 : <the posted statement> := by
         exact PEqualNP.Outside.L_gct_101.helper ...

## The plain-file rules

A proof file is only imports, then definitions, lemmas and one theorem with their proofs. A
file that follows the five rules below is merged by a program as soon as the check accepts it.
A file that breaks one is refused, or waits for a person to read it.

1. Nothing that runs code while the file compiles: no `initialize`, no `#eval` or any other
   `#` command, no `macro`, `syntax`, `notation` or `elab`, no `attribute` command, no
   `native_decide`.
2. Comments: start every comment line with two hyphens, or indent the text of a block comment.
   Open a block comment at the start of a line and close it at the end of one. No `#` headings.
   A word from rule 1 is refused even inside a comment, so reword it. The simplest file has no
   comments at all.
3. No double quotes anywhere: no string literals.
4. Options: only `maxRecDepth`, `maxHeartbeats`, `synthInstance.maxSize` and
   `synthInstance.maxHeartbeats`, each on its own line of the form
   `set_option <name> <number> in`, directly above the declaration it serves. The only
   attributes are `@[simp]` and `@[local simp]`.
5. Use Mathlib's types where you can. A file that declares its own data type or instance is
   not merged by the program: it waits for a person to read it.

## How it is checked

1. A check runs on the pull request and prints a verdict. It is a quick answer for you. It is
   advisory.
2. A second check is started by the maintainers from the base branch. It takes your one file as
   data, reads the statement from the desk's public list, and runs the checker of the base
   branch. Its verdict is the one that counts.
3. On `ACCEPTED` the pull request is merged and the lemma is recorded as checked. Credit goes
   to the author of the pull request.

## What is not read

The description of a pull request is not read. Neither are its title, its comments or its
commit messages. Only the one file is used, and only the checker judges it. Put nothing there
that you need anyone to see.

## Words

A lemma here is "checked". Please do not describe a proof in any other terms in this
repository.
