LIB := AaronsonAmbainis

.PHONY: check imports audit build axioms replay replay-fresh count digest \
        comparator comparator-unsandboxed comparator-controls paper clean

# The checks that every change must pass.
check: imports audit build axioms

# All project-local imports resolve, every file of the library is reached from the root, the
# statement file imports Mathlib only, and the two comparator modules stand apart: no file imports
# them, and the challenge imports the statement file only.
imports:
	python3 scripts/check_local_imports.py . $(LIB)

# The source text has no placeholder, no assumption, no way around the kernel, no new syntax.
# The one exception is declared here: the challenge of the comparator run states the four final
# theorems and leaves their proofs open, so it contains the word `sorry` exactly four times.
audit:
	python3 scripts/check_no_placeholders.py $(LIB) $(LIB).lean audit/OriginalConjecture6.lean \
		--holes $(LIB)/Comparator/Challenge.lean=4 --json notes/source-audit.json

# Compile the project.
build:
	lake build
	lake env lean audit/OriginalConjecture6.lean

# Print the axioms on which the final theorems depend and check the list.
axioms:
	./scripts/print_axioms.sh 2>&1 | tee axiom-report.txt
	python3 scripts/check_axioms.py axiom-report.txt

# Replay every declaration of the project through the kernel, outside the elaborator.
replay:
	lake env leanchecker -v $(LIB)

# Replay everything on which the final theorems depend, Lean core and Mathlib included, from an
# empty environment. This needs about 9 GB of memory and about 27 minutes.
replay-fresh:
	lake env leanchecker --fresh $(LIB).Main

# Count the declarations stored in the compiled files of the project (for comparison with the
# number that a kernel replay reports).
count:
	lake env lean --run scripts/count_declarations.lean

# One digest of the Lean project files; the recorded checks name the digest on which they ran.
digest:
	python3 scripts/source_digest.py . $(LIB)

# Comparator (https://github.com/leanprover/comparator): the statements of the challenge against
# the proofs of the solution, in a sandbox. Linux only; see comparator/README.md for the tools.
comparator:
	./scripts/run_comparator.sh

# The same run without the sandbox. It tests the setup and certifies nothing.
comparator-unsandboxed:
	./scripts/run_comparator_unsandboxed.sh

# Five small sandboxed runs on verification/control/: one that comparator must accept and four
# that it must reject.
comparator-controls:
	./scripts/run_comparator_controls.sh

paper:
	$(MAKE) -C paper

clean:
	rm -f axiom-report.txt build.log
