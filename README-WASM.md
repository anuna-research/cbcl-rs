# CBCL WebAssembly Compilation

This directory contains a complete pipeline for compiling the CBCL (Collaborative Bootstrapped Communication Language) system to WebAssembly using Hoot from the Spritely Institute.

## Overview

The WASM compilation pipeline allows CBCL agents to run in web browsers with full functionality, including:

- Agent creation and message parsing
- Dialect system with runtime verification
- Multi-agent environments
- Gossip protocol for dialect propagation
- Planning dialect capabilities

## Prerequisites

- GNU Guile 3.0 or later
- Git (for cloning Hoot)
- Python 3 (for local web server)
- A modern browser with WebAssembly GC support:
  - Chrome 119+
  - Firefox 120+
  - Safari 17+

## Quick Start

1. **Install Hoot:**
   ```bash
   make setup-hoot
   source setup-hoot-env.sh
   ```

2. **Build CBCL to WASM:**
   ```bash
   make build-wasm
   ```

3. **Test in browser:**
   ```bash
   make serve-wasm
   # Open http://localhost:8080/demo.html
   ```

## Architecture

The WASM compilation pipeline consists of:

### Core Components

- **`build-wasm.scm`**: Main build script that orchestrates compilation
- **`wasm-cbcl-wrapper.scm`**: WASM-compatible wrapper functions
- **`hoot-setup.sh`**: Automated Hoot installation script

### Generated Files

- **`wasm-build/cbcl.wasm`**: Core CBCL module compiled to WASM
- **`wasm-build/cbcl-gossip.wasm`**: Gossip protocol module
- **`wasm-build/dialects-cbcl-planning.wasm`**: Planning dialect module
- **`wasm-build/cbcl-interface.js`**: JavaScript API wrapper
- **`wasm-build/demo.html`**: Interactive demo page

## JavaScript API

The compiled WASM modules provide a JavaScript API for web applications:

```javascript
import { loadCBCL } from './cbcl-interface.js';

// Load CBCL WASM module
const cbcl = await loadCBCL('./cbcl.wasm');

// Create an agent
const agent = await cbcl.createAgent('web-agent');

// Parse and evaluate messages
const message = agent.parseMessage('(tell bob "hello from browser")');
const result = agent.evaluateMessage(message);

// Create multi-agent environment
const env = cbcl.createEnvironment();
env.createAgent('agent1');
env.createAgent('agent2');
env.sendMessage('agent1', 'agent2', '(ask status)');
```

## Browser Demo

The demo page (`demo.html`) provides an interactive interface to:

- Create CBCL agents in the browser
- Parse and evaluate CBCL messages
- Test multi-agent communication
- Explore dialect capabilities

## Performance Characteristics

WASM compilation provides several benefits:

- **Near-native performance**: WASM executes much faster than interpreted JavaScript
- **Memory safety**: Automatic garbage collection via WASM GC
- **Sandboxing**: Safe execution in browser environment
- **Portability**: Runs on any WASM-compatible browser

## Limitations

Current WASM implementation has some constraints:

- **Dialect verification**: Simplified cryptographic checks
- **File I/O**: Limited to browser capabilities
- **Networking**: Subject to browser CORS policies
- **Debugging**: Limited debugging tools compared to native Guile

## Development Workflow

For iterative development:

1. Modify CBCL source files in `src/`
2. Rebuild with `make build-wasm`
3. Test changes in browser with `make serve-wasm`
4. Debug using browser developer tools

## Integration with Web Applications

To integrate CBCL WASM into your web application:

1. Copy the generated WASM files and JavaScript interface
2. Import the CBCL API in your application
3. Initialize agents and environments as needed
4. Use CBCL for agent-based communication and planning

Example integration:

```html
<!DOCTYPE html>
<html>
<head>
    <script type="module">
        import { loadCBCL } from './cbcl-interface.js';
        
        async function initializeCBCL() {
            const cbcl = await loadCBCL('./cbcl.wasm');
            
            // Create planning agents for your application
            const plannerAgent = await cbcl.createAgent('planner');
            const executorAgent = await cbcl.createAgent('executor');
            
            // Install planning dialect
            plannerAgent.installDialect(planningDialectDef);
            
            // Your application logic here
        }
        
        initializeCBCL();
    </script>
</head>
<body>
    <!-- Your web application UI -->
</body>
</html>
```

## Troubleshooting

**Build Issues:**
- Ensure Hoot is properly installed: `source setup-hoot-env.sh`
- Check Guile version: `guile --version` (should be 3.0+)
- Verify CBCL source files compile: `make check`

**Runtime Issues:**
- Check browser console for JavaScript errors
- Verify WASM GC support in your browser
- Ensure files are served over HTTP (not file://)

**Performance Issues:**
- Enable WASM optimizations in browser settings
- Use production build flags in Hoot compilation
- Profile using browser developer tools

## Contributing

To extend the WASM compilation pipeline:

1. Add new CBCL modules to `cbcl-modules` list in `build-wasm.scm`
2. Update JavaScript interface in generated `cbcl-interface.js`
3. Add corresponding demo functionality to `demo.html`
4. Test thoroughly in multiple browsers

## Future Enhancements

Planned improvements:

- **Streaming compilation**: Support for large CBCL codebases
- **Hot reloading**: Live updates during development
- **Performance profiling**: Built-in performance monitoring
- **Advanced debugging**: Source map support for CBCL code
- **Npm package**: Easy installation via package managers
