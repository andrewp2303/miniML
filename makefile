all: evaluation expr miniml tests test_s expressions

evaluation: evaluation.ml
	ocamlbuild -use-ocamlfind evaluation.byte

expr: expr.ml
	ocamlbuild -use-ocamlfind expr.byte

miniml: miniml.ml
	ocamlbuild -use-ocamlfind miniml.byte

tests: tests.ml
	ocamlbuild -use-ocamlfind tests.byte

test_s: test_simple.ml
	ocamlbuild -use-ocamlfind test_simple.byte

expressions: expressions.ml
	ocamlbuild -use-ocamlfind expressions.byte

clean:
	rm -rf _build *.byte