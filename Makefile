.PHONY: default lstar lstar-rocq install uninstall test clean fmt
.IGNORE: fmt

OPAM ?= opam
OPAM_EXEC ?= $(OPAM) exec --
DUNE ?= dune

default: lstar lstar-rocq

fmt: lstar-rocq
	$(OPAM_EXEC) $(DUNE) build @fmt
	$(OPAM_EXEC) $(DUNE) promote

lstar-rocq:
	-$(OPAM_EXEC) $(DUNE) build -p lstar-rocq

lstar: lstar-rocq
	$(OPAM_EXEC) $(DUNE) build

clean:
	$(OPAM_EXEC) $(DUNE) clean
	git clean -dfXq

test: fmt
	$(OPAM_EXEC) $(DUNE) exec lstar.alternating | grep Accuracy
	$(OPAM_EXEC) $(DUNE) exec lstar.alternating_socket | grep Accuracy
	$(OPAM_EXEC) $(DUNE) exec lstar.mod3 | grep Accuracy
	$(OPAM_EXEC) $(DUNE) exec lstar.div7 | grep Accuracy
	$(OPAM_EXEC) $(DUNE) exec lstar.traffic | grep Accuracy
	$(OPAM_EXEC) $(DUNE) exec lstar.vending | grep Accuracy

DOCS_PATH=docs/
DOCS_NAME=lstar
DOCS_DESCR=L* implementation in Rocq
DOCS_INDEX_TITLE=$(DOCS_NAME) - $(DOCS_DESCR)
define DOCS_EMBED
<meta content="$(DOCS_NAME)" property="og:title" />\
<meta content="$(DOCS_DESCR)" property="og:description" />\
<meta content="https://github.com/CharlesAverill/lstar-rocq" property="og:url" />
endef

cleandocs:
	if [ ! -d $(DOCS_PATH) ]; then \
		mkdir $(DOCS_PATH); \
	fi
	rm -rf $(DOCS_PATH)lstar-rocq $(DOCS_PATH)odoc.support $(DOCS_PATH)*.html $(DOCS_PATH)*.css

docs: clean cleandocs lstar-rocq
	$(OPAM_EXEC) rocq doc --multi-index -g --utf8 _build/default/theories/*.v -d $(DOCS_PATH)
	
	@echo "Preparing Index\n--------------"
	# Header
	sed -i 's/<title>.*<\/title>/<title>$(DOCS_INDEX_TITLE)<\/title>/g' $(DOCS_PATH)index.html
	sed -i 's@</head>@$(DOCS_EMBED)\n</head>@g' $(DOCS_PATH)index.html
	sed -i 's/..\/odoc.support/odoc.support/g' $(DOCS_PATH)index.html
	sed -i 's/lstar.//g' $(DOCS_PATH)index.html

push: cleandocs lstar lstar-rocq
	@read -p "Commit message: " input; \
	if [ -z "$input" ]; then \
		echo "Error: Please provide a valid commit message."; \
		exit 1; \
	fi; \
	git add . && git commit -m "$$input" && git push origin main
