#!/bin/bash

# CBCL WASM Package Build Script
# Builds the complete CBCL WebAssembly package

set -e

echo "🔨 Building CBCL WASM Package..."

# Check if we're in the right directory
if [ ! -f "package.json" ]; then
    echo "❌ Error: Must be run from the cbcl-wasm-package directory"
    exit 1
fi

# Clean previous build
echo "🧹 Cleaning previous build..."
rm -rf dist/*

# Build WASM from source
echo "⚙️ Building WASM from Scheme source..."
cd ..
if [ ! -f "setup-hoot-env.sh" ]; then
    echo "❌ Error: setup-hoot-env.sh not found in parent directory"
    exit 1
fi

source setup-hoot-env.sh
make clean-wasm
make build-wasm
./fix-wasm-build.sh

# Copy built files to package
echo "📦 Copying files to package..."
cd cbcl-wasm-package

# Copy JavaScript interface
cp src/cbcl-wasm.js dist/
cp src/cbcl-wasm.d.ts dist/

# Copy WASM files
cp ../wasm-build/cbcl-hoot.wasm dist/
cp ../wasm-build/reflect.js dist/
cp ../wasm-build/reflect.wasm dist/
cp ../wasm-build/wtf8.wasm dist/

# Copy other required files
cp README.md dist/
cp LICENSE dist/
cp package.json dist/

echo "✅ Build completed successfully!"
echo ""
echo "📊 Package Contents:"
ls -la dist/

echo ""
echo "🧪 Running tests..."
npm test

echo ""
echo "📋 Package ready for:"
echo "  • npm publish (for npm registry)"
echo "  • Local testing (npm run serve)"
echo "  • Browser testing (open test/browser-test.html)"
echo ""
echo "🎉 CBCL WASM Package build complete!"
