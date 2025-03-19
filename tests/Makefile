all: compile run

compile:
	@echo "Compiling jit_eval.ml..."
	eval $$(opam env) && \
	ocamlc -c jit_eval.ml && \
	ocamlfind ocamlc -o jit -package yojson -linkpkg jit_eval.cmo jit.ml

run:
	@echo "Running jit..."
	./jit

clean:
	@echo "Cleaning up..."
	rm -f jit jit_eval.cmi jit_eval.cmo

.PHONY: all compile run clean
