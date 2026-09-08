# Makefile for CBCL Internet-Draft

# The draft stem. The Markdown source is $(DRAFT).md and every generated
# artefact shares the stem, so renaming the draft is a one-line change here.
DRAFT := draft-oconnor-cbcl

# Auto-detect tool paths
KRAMDOWN_RFC := $(shell command -v kramdown-rfc 2>/dev/null || \
                  command -v kramdown-rfc2629 2>/dev/null || \
                  ls /opt/homebrew/lib/ruby/gems/*/bin/kramdown-rfc 2>/dev/null | head -1 || \
                  ls $(HOME)/.gem/ruby/*/bin/kramdown-rfc 2>/dev/null | head -1)
XML2RFC := $(shell command -v xml2rfc 2>/dev/null)
WEASYPRINT := $(shell command -v weasyprint 2>/dev/null)

.PHONY: all clean help force check-tools pdf

# xml2rfc writes TXT and HTML together; force also requires clean before all.
.NOTPARALLEL:

all: check-tools $(DRAFT).txt $(DRAFT).html pdf ## Generate all output formats

force: clean all ## Force rebuild (clean + build)

check-tools:
	@if [ -z "$(KRAMDOWN_RFC)" ]; then \
		echo "Error: kramdown-rfc not found. Install with: gem install kramdown-rfc"; \
		exit 1; \
	fi
	@if [ -z "$(XML2RFC)" ]; then \
		echo "Error: xml2rfc not found. Install with: pip install xml2rfc"; \
		exit 1; \
	fi

$(DRAFT).xml: $(DRAFT).md
	@echo "Generating XML from Markdown..."
	@$(KRAMDOWN_RFC) $(DRAFT).md > $(DRAFT).xml

$(DRAFT).txt $(DRAFT).html: $(DRAFT).xml
	@echo "Generating TXT and HTML from XML..."
	@$(XML2RFC) $(DRAFT).xml --text --html

pdf: $(DRAFT).html ## Generate PDF from HTML (requires weasyprint)
	@if [ -z "$(WEASYPRINT)" ]; then \
		echo "Warning: weasyprint not found. PDF generation skipped."; \
		echo "Install with: pip install weasyprint"; \
	else \
		echo "Generating PDF from HTML..."; \
		$(WEASYPRINT) $(DRAFT).html $(DRAFT).pdf; \
	fi

clean: ## Remove generated files
	@echo "Cleaning generated files..."
	@rm -f $(DRAFT).xml $(DRAFT).txt $(DRAFT).html $(DRAFT).pdf
	@rm -rf .refcache
	@echo "Done."

help: ## Show this help message
	@echo "CBCL Internet-Draft Build System"
	@echo ""
	@echo "Usage: make [target]"
	@echo ""
	@echo "Draft stem: $(DRAFT)"
	@echo ""
	@echo "Targets:"
	@grep -E '^[a-zA-Z_-]+:.*?## .*$$' $(MAKEFILE_LIST) | awk 'BEGIN {FS = ":.*?## "}; {printf "  %-15s %s\n", $$1, $$2}'
