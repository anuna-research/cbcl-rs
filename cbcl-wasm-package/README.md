# CBCL WebAssembly Package

A complete WebAssembly implementation of CBCL (Chat-based Communication Language) that provides agent-based communication, multi-agent environments, and gossip-based dialect propagation.

## Features

- 🤖 **Agent Creation & Management** - Create and manage CBCL agents
- 💬 **Message Passing** - Support for tell, ask, and reply messages  
- 🌐 **Multi-Agent Environments** - Manage multiple agents with conversation tracking
- 🗣️ **Gossip Networks** - Epidemic dialect propagation across agent networks
- ⚡ **WebAssembly Performance** - Compiled from Scheme using Hoot for optimal performance
- 🧪 **Comprehensive Testing** - Full test suite with performance and integration tests

## Installation

```bash
npm install cbcl-wasm
```

## Quick Start

### Basic Usage

```javascript
// Load the CBCL WASM module
const cbcl = await loadCBCL('./cbcl-hoot.wasm');

// Create a simple agent
const alice = await cbcl.createAgent('alice');

// Send messages
const tellResult = alice.tell('bob', 'Hello Bob!');
const askResult = alice.ask('bob', 'How are you?');
const replyResult = alice.reply('I am fine, thank you!');

console.log(tellResult); // { success: true, operation: 'tell', ... }
```

### Multi-Agent Environment

```javascript
// Create an environment for multiple agents
const env = cbcl.createEnvironment();

// Create agents within the environment
const alice = await env.createAgent('alice');
const bob = await env.createAgent('bob');
const charlie = await env.createAgent('charlie');

// Send messages between agents
env.sendMessage('alice', 'bob', 'Hello Bob!');
env.sendMessage('bob', 'alice', 'Hi Alice!');

// Track conversations
const conversation = env.getConversation('alice', 'bob');
console.log(conversation); // Array of message objects

// Get environment statistics
const stats = env.getStats();
console.log(stats); // { agentCount: 3, messageCount: 2, ... }
```

### Gossip Networks

```javascript
// Create a gossip network for dialect propagation
const network = cbcl.createGossipNetwork();

// Add agents to the network
const agents = [];
for (let i = 0; i < 10; i++) {
  const agent = await cbcl.createAgent(`agent${i}`);
  network.addAgent(agent);
  agents.push(agent);
}

// Define and propagate a dialect
const dialectSpec = {
  name: 'greeting-dialect',
  performatives: ['greet', 'farewell'],
  examples: [
    '(greet alice "Good morning!")',
    '(farewell bob "See you later!")'
  ]
};

const propagation = network.propagateDialect('greeting-dialect', dialectSpec);

// Simulate gossip propagation steps
while (true) {
  const step = network.gossipStep(propagation.propagationId);
  console.log(`Round ${step.round}: ${step.newInfections} new infections`);
  
  if (step.converged) {
    console.log('Dialect fully propagated!');
    break;
  }
}
```

### Message Parsing

```javascript
const agent = await cbcl.createAgent('parser');

// Parse CBCL message strings
const tellParsed = agent.parseMessage('(tell bob "Hello World")');
const askParsed = agent.parseMessage('(ask charlie "What time is it?")');
const replyParsed = agent.parseMessage('(reply "It is 3:30 PM")');

// Evaluate parsed messages
const result = agent.evaluateMessage(tellParsed.data.parsed);
console.log(result); // Evaluation result
```

## API Reference

### Classes

#### `CBCL`
Main entry point for the CBCL system.

**Methods:**
- `createAgent(agentId)` - Create a standalone agent
- `createEnvironment(envId?)` - Create a multi-agent environment  
- `createGossipNetwork(networkId?)` - Create a gossip network
- `runDemo()` - Run a demo conversation
- `test()` - Run basic functionality tests

#### `CBCLAgent`
Represents a single CBCL agent.

**Methods:**
- `getId()` - Get the agent's ID
- `tell(recipient, content)` - Send a tell message
- `ask(recipient, query)` - Send an ask message  
- `reply(content)` - Send a reply message
- `parseMessage(messageStr)` - Parse a CBCL message string
- `evaluateMessage(message)` - Evaluate a parsed message

#### `CBCLEnvironment`
Manages multiple agents and their interactions.

**Methods:**
- `createAgent(agentId)` - Create an agent in this environment
- `getAgent(agentId)` - Get an existing agent
- `sendMessage(fromId, toId, message)` - Send a message between agents
- `listAgents()` - List all agent IDs
- `getStats()` - Get environment statistics
- `getConversation(agent1, agent2)` - Get conversation history
- `reset()` - Reset the environment

#### `CBCLGossipNetwork`
Implements epidemic dialect propagation.

**Methods:**
- `addAgent(agent)` - Add an agent to the network
- `propagateDialect(dialectName, dialectSpec)` - Start dialect propagation
- `gossipStep(propagationId)` - Simulate one gossip step
- `getNetworkStats()` - Get network statistics

### Functions

#### `loadCBCL(wasmUrl, options?)`
Load and initialize the CBCL WASM module.

**Parameters:**
- `wasmUrl` - URL to the CBCL WASM file
- `options` - Loading options object
  - `reflect_wasm_dir` - Directory containing Hoot reflect files
  - `user_imports` - Custom imports for the WASM module

**Returns:** Promise resolving to a `CBCL` instance

## Building from Source

```bash
# Clone the repository
git clone https://github.com/cbcl/cbcl-wasm.git
cd cbcl-wasm

# Install dependencies and build
npm install
npm run build

# Run tests
npm test

# Start development server
npm run serve
```

## Requirements

- Node.js 14+ (for development and testing)
- Modern browser with WebAssembly GC support
- Hoot (for building from Scheme source)

## Testing

The package includes comprehensive tests covering:

- Basic agent functionality
- Environment management
- Message passing and parsing
- Gossip network simulation
- Performance benchmarks
- Error handling
- Integration scenarios

```bash
# Run Node.js tests
npm test

# Run browser tests
npm run test:browser
```

## Performance

The CBCL WASM package is optimized for performance:

- ⚡ WebAssembly execution speed
- 🔄 Efficient agent creation (100 agents < 5s)
- 📨 Fast message passing (1000 messages < 5s)
- 🧠 Minimal memory footprint
- 🌐 Suitable for real-time applications

## Examples

Check the `examples/` directory for complete usage examples:

- Basic agent communication
- Multi-agent chat rooms
- Dialect propagation simulations
- Performance benchmarks

## Contributing

1. Fork the repository
2. Create a feature branch
3. Make your changes
4. Add tests for new functionality
5. Run the test suite
6. Submit a pull request

## License

MIT License - see LICENSE file for details.

## Related Projects

- [CBCL Specification](https://github.com/cbcl/cbcl-spec) - Formal specification
- [CBCL Paper](https://github.com/cbcl/cbcl-paper) - Academic paper and validation
- [Hoot](https://spritely.institute/hoot/) - Scheme to WebAssembly compiler

## Support

- 📖 [Documentation](https://cbcl.github.io/cbcl-wasm/)
- 🐛 [Issue Tracker](https://github.com/cbcl/cbcl-wasm/issues)
- 💬 [Discussions](https://github.com/cbcl/cbcl-wasm/discussions)
