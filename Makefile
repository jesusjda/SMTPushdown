CONVERT_LIBS=-use-ocamlfind -pkg sexplib,str,num
OPTS=-cflags -warn-error,+a

default: convert.native

all: convert.native

convert.native: *.ml */*.ml
	ocamlbuild ${OPTS} ${CONVERT_LIBS} convert.native

clean:
	ocamlbuild -clean
