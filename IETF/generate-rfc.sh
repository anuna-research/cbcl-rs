#!/bin/bash
#
# generate-rfc.sh
#
# Generate RFC format outputs (XML, TXT, HTML) from markdown source
# using kramdown-rfc and xml2rfc toolchain

set -e  # Exit on error

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Script directory
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

# Source file
DRAFT_NAME="draft-oconnor-cbcl"
SOURCE_MD="${DRAFT_NAME}.md"

echo "================================================"
echo "  IETF Internet-Draft Generator"
echo "================================================"
echo ""

# Check if source file exists
if [ ! -f "$SOURCE_MD" ]; then
    echo -e "${RED}Error: Source file $SOURCE_MD not found${NC}"
    exit 1
fi

echo "Source: $SOURCE_MD"
echo ""

# Check for required tools
echo "Checking for required tools..."

# Check for kramdown-rfc
if ! command -v kramdown-rfc &> /dev/null; then
    # Try to find it in common gem installation paths
    # Note: the glob must be unquoted to expand, and the gem may be under
    # either the Homebrew tree or the user gem dir.
    KRAMDOWN_RFC=$(ls /opt/homebrew/lib/ruby/gems/*/bin/kramdown-rfc \
                      "$HOME"/.gem/ruby/*/bin/kramdown-rfc 2>/dev/null | head -1)
    if [ -z "$KRAMDOWN_RFC" ]; then
        echo -e "${RED}Error: kramdown-rfc not found${NC}"
        echo "Install with: gem install kramdown-rfc"
        exit 1
    fi
else
    KRAMDOWN_RFC="kramdown-rfc"
fi

echo -e "${GREEN}✓${NC} kramdown-rfc found: $KRAMDOWN_RFC"

# Check for xml2rfc
if ! command -v xml2rfc &> /dev/null; then
    echo -e "${RED}Error: xml2rfc not found${NC}"
    echo "Install with: pip install xml2rfc"
    exit 1
fi

echo -e "${GREEN}✓${NC} xml2rfc found: $(command -v xml2rfc)"

# Check for weasyprint (optional, for PDF generation)
if command -v weasyprint &> /dev/null; then
    HAS_WEASYPRINT=true
    echo -e "${GREEN}✓${NC} weasyprint found: $(command -v weasyprint)"
else
    HAS_WEASYPRINT=false
    echo -e "${YELLOW}⚠${NC}  weasyprint not found (PDF generation will be skipped)"
    echo "    Install with: pip install weasyprint"
fi
echo ""

# Step 1: Generate XML from Markdown
echo "Step 1: Generating XML from Markdown..."
if "$KRAMDOWN_RFC" "$SOURCE_MD" > "${DRAFT_NAME}.xml"; then
    echo -e "${GREEN}✓${NC} XML generated successfully"
else
    echo -e "${RED}✗${NC} Failed to generate XML"
    exit 1
fi
echo ""

# Step 2: Generate TXT and HTML from XML
echo "Step 2: Generating TXT and HTML from XML..."
if xml2rfc "${DRAFT_NAME}.xml" --text --html 2>&1; then
    echo -e "${GREEN}✓${NC} TXT and HTML generated successfully"
else
    echo -e "${RED}✗${NC} Failed to generate TXT and HTML (check output above)"
    exit 1
fi
echo ""

# Step 3: Generate PDF from HTML (if weasyprint is available)
if [ "$HAS_WEASYPRINT" = true ]; then
    echo "Step 3: Generating PDF from HTML..."
    if [ -f "${DRAFT_NAME}.html" ]; then
        if weasyprint "${DRAFT_NAME}.html" "${DRAFT_NAME}.pdf" 2>&1; then
            echo -e "${GREEN}✓${NC} PDF generated successfully"
        else
            echo -e "${YELLOW}⚠${NC}  PDF generation completed with warnings"
        fi
    else
        echo -e "${RED}✗${NC} Cannot generate PDF: HTML file not found"
    fi
    echo ""
fi

# Show generated files
echo "================================================"
echo "  Generated Files"
echo "================================================"
echo ""

if [ -f "${DRAFT_NAME}.xml" ]; then
    XML_SIZE=$(ls -lh "${DRAFT_NAME}.xml" | awk '{print $5}')
    echo -e "${GREEN}✓${NC} ${DRAFT_NAME}.xml   ($XML_SIZE)"
else
    echo -e "${RED}✗${NC} ${DRAFT_NAME}.xml   (missing)"
fi

if [ -f "${DRAFT_NAME}.txt" ]; then
    TXT_SIZE=$(ls -lh "${DRAFT_NAME}.txt" | awk '{print $5}')
    TXT_LINES=$(wc -l < "${DRAFT_NAME}.txt")
    echo -e "${GREEN}✓${NC} ${DRAFT_NAME}.txt   ($TXT_SIZE, $TXT_LINES lines)"
else
    echo -e "${RED}✗${NC} ${DRAFT_NAME}.txt   (missing)"
fi

if [ -f "${DRAFT_NAME}.html" ]; then
    HTML_SIZE=$(ls -lh "${DRAFT_NAME}.html" | awk '{print $5}')
    echo -e "${GREEN}✓${NC} ${DRAFT_NAME}.html  ($HTML_SIZE)"
else
    echo -e "${RED}✗${NC} ${DRAFT_NAME}.html  (missing)"
fi

if [ -f "${DRAFT_NAME}.pdf" ]; then
    PDF_SIZE=$(ls -lh "${DRAFT_NAME}.pdf" | awk '{print $5}')
    PDF_PAGES=$(pdfinfo "${DRAFT_NAME}.pdf" 2>/dev/null | grep "Pages:" | awk '{print $2}')
    if [ -n "$PDF_PAGES" ]; then
        echo -e "${GREEN}✓${NC} ${DRAFT_NAME}.pdf   ($PDF_SIZE, $PDF_PAGES pages)"
    else
        echo -e "${GREEN}✓${NC} ${DRAFT_NAME}.pdf   ($PDF_SIZE)"
    fi
else
    if [ "$HAS_WEASYPRINT" = true ]; then
        echo -e "${RED}✗${NC} ${DRAFT_NAME}.pdf   (missing)"
    else
        echo -e "${YELLOW}⊘${NC} ${DRAFT_NAME}.pdf   (skipped - weasyprint not installed)"
    fi
fi

echo ""
echo "================================================"
echo "  Complete!"
echo "================================================"
echo ""
echo "Next steps:"
echo "  • Review: open ${DRAFT_NAME}.html"
if [ -f "${DRAFT_NAME}.pdf" ]; then
    echo "  • Review: open ${DRAFT_NAME}.pdf"
fi
echo "  • Submit: ${DRAFT_NAME}.txt to https://datatracker.ietf.org/submit/"
echo ""
