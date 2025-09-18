# Makefile for Paper 3 LaTeX documents
# Usage: make [target]
# Targets: all, paper3, paper3a, paper3b, paper3b-add1, formalization, clean

# LaTeX compiler
LATEX = pdflatex
BIBTEX = bibtex
LATEXFLAGS = -interaction=nonstopmode

# Main documents
PAPER3 = Paper3_Main
PAPER3A = Paper3A_Publication
PAPER3B = Paper3B_Publication
PAPER3B_ADD1 = Paper3B_Addendum1
FORMALIZATION = Paper3_Lean_Formalization

# All main targets
PDFS = $(PAPER3).pdf $(PAPER3A).pdf $(PAPER3B).pdf $(PAPER3B_ADD1).pdf $(FORMALIZATION).pdf

# Default target
all: $(PDFS)

# Individual paper targets
paper3: $(PAPER3).pdf
paper3a: $(PAPER3A).pdf
paper3b: $(PAPER3B).pdf
paper3b-add1: $(PAPER3B_ADD1).pdf
formalization: $(FORMALIZATION).pdf

# Generic rule for building PDFs
%.pdf: %.tex paper3-macros.tex
	$(LATEX) $(LATEXFLAGS) $<
	-$(BIBTEX) $(basename $<)
	$(LATEX) $(LATEXFLAGS) $<
	$(LATEX) $(LATEXFLAGS) $<

# Quick build (single pass, no bibtex)
quick-%: %.tex paper3-macros.tex
	$(LATEX) $(LATEXFLAGS) $<

# Clean auxiliary files
clean:
	rm -f *.aux *.log *.bbl *.blg *.out *.toc *.lof *.lot *.fls *.fdb_latexmk

# Clean everything including PDFs
distclean: clean
	rm -f $(PDFS)

# Watch for changes and rebuild (requires latexmk)
watch-%: %.tex
	latexmk -pdf -pvc -interaction=nonstopmode $<

# Help target
help:
	@echo "Paper 3 LaTeX Makefile"
	@echo ""
	@echo "Usage: make [target]"
	@echo ""
	@echo "Targets:"
	@echo "  all           - Build all papers (default)"
	@echo "  paper3        - Build Paper3_Main.pdf"
	@echo "  paper3a       - Build Paper3A_Publication.pdf"
	@echo "  paper3b       - Build Paper3B_Publication.pdf"
	@echo "  formalization - Build Paper3_Lean_Formalization.pdf"
	@echo "  quick-[name]  - Quick single-pass build (no bibliography)"
	@echo "  watch-[name]  - Watch and auto-rebuild on changes (requires latexmk)"
	@echo "  clean         - Remove auxiliary files"
	@echo "  distclean     - Remove all generated files including PDFs"
	@echo "  help          - Show this help message"

.PHONY: all paper3 paper3a paper3b formalization clean distclean help