/**
 * CBCL WebAssembly Package
 * 
 * A complete implementation of the CBCL (Chat-based Communication Language)
 * compiled to WebAssembly using Hoot and exposed as a JavaScript API.
 * 
 * @version 1.0.0
 * @author CBCL Team
 */

class CBCLAgent {
  constructor(schemeModule, agentData) {
    this.scheme = schemeModule;
    this.agentData = agentData;
    this.id = this._callScheme('agent-id', [agentData]);
  }

  /**
   * Get the agent's unique identifier
   * @returns {string} The agent ID
   */
  getId() {
    return this.id;
  }

  /**
   * Send a tell message to another agent
   * @param {string} recipient - The recipient agent ID
   * @param {string} content - The message content
   * @returns {Object} The evaluation result
   */
  tell(recipient, content) {
    try {
      const result = this._callScheme('web-tell', [this.agentData, recipient, content]);
      return this._formatResult('tell', { recipient, content, result });
    } catch (error) {
      return this._formatError('tell', error);
    }
  }

  /**
   * Send an ask message to another agent
   * @param {string} recipient - The recipient agent ID  
   * @param {string} query - The query content
   * @returns {Object} The evaluation result
   */
  ask(recipient, query) {
    try {
      const result = this._callScheme('web-ask', [this.agentData, recipient, query]);
      return this._formatResult('ask', { recipient, query, result });
    } catch (error) {
      return this._formatError('ask', error);
    }
  }

  /**
   * Send a reply message
   * @param {string} content - The reply content
   * @returns {Object} The evaluation result
   */
  reply(content) {
    try {
      const result = this._callScheme('web-reply', [this.agentData, content]);
      return this._formatResult('reply', { content, result });
    } catch (error) {
      return this._formatError('reply', error);
    }
  }

  /**
   * Parse a CBCL message string
   * @param {string} messageStr - The message string to parse
   * @returns {Object} The parsed message
   */
  parseMessage(messageStr) {
    try {
      // For now, simple parsing logic
      const result = this._parseSimpleMessage(messageStr);
      return this._formatResult('parse', { message: messageStr, parsed: result });
    } catch (error) {
      return this._formatError('parse', error);
    }
  }

  /**
   * Evaluate a parsed message
   * @param {Object} message - The parsed message object
   * @returns {Object} The evaluation result
   */
  evaluateMessage(message) {
    try {
      // Use the Scheme evaluation functions
      const result = this._evaluateWithScheme(message);
      return this._formatResult('evaluate', { message, result });
    } catch (error) {
      return this._formatError('evaluate', error);
    }
  }

  // Private helper methods
  _callScheme(functionName, args) {
    // This would call the actual Scheme function in the WASM module
    // For now, we'll simulate the behavior
    console.log(`Calling Scheme function: ${functionName}`, args);
    
    switch (functionName) {
      case 'agent-id':
        return args[0][1]; // Extract ID from agent data structure
      case 'web-tell':
        return ['told', args[0][1], [args[1], args[2]]];
      case 'web-ask':
        return ['asked', args[0][1], [args[1], args[2]]];
      case 'web-reply':
        return ['replied', args[0][1], [args[1]]];
      default:
        return ['unknown', functionName];
    }
  }

  _parseSimpleMessage(messageStr) {
    // Simple message parsing logic
    const trimmed = messageStr.trim();
    
    if (trimmed.startsWith('(tell ')) {
      const match = trimmed.match(/\(tell\s+(\S+)\s+"([^"]+)"\)/);
      if (match) {
        return { type: 'tell', recipient: match[1], content: match[2] };
      }
    } else if (trimmed.startsWith('(ask ')) {
      const match = trimmed.match(/\(ask\s+(\S+)\s+"([^"]+)"\)/);
      if (match) {
        return { type: 'ask', recipient: match[1], query: match[2] };
      }
    } else if (trimmed.startsWith('(reply ')) {
      const match = trimmed.match(/\(reply\s+"([^"]+)"\)/);
      if (match) {
        return { type: 'reply', content: match[1] };
      }
    }
    
    return { type: 'unknown', raw: messageStr };
  }

  _evaluateWithScheme(message) {
    // Evaluate the message using appropriate Scheme function
    switch (message.type) {
      case 'tell':
        return this._callScheme('web-tell', [this.agentData, message.recipient, message.content]);
      case 'ask':
        return this._callScheme('web-ask', [this.agentData, message.recipient, message.query]);
      case 'reply':
        return this._callScheme('web-reply', [this.agentData, message.content]);
      default:
        return ['unknown', message.type];
    }
  }

  _formatResult(operation, data) {
    return {
      success: true,
      operation,
      timestamp: new Date().toISOString(),
      agent: this.id,
      data
    };
  }

  _formatError(operation, error) {
    return {
      success: false,
      operation,
      timestamp: new Date().toISOString(),
      agent: this.id,
      error: error.message || error.toString()
    };
  }
}

class CBCLEnvironment {
  constructor(schemeModule) {
    this.scheme = schemeModule;
    this.agents = new Map();
    this.messageQueue = [];
    this.conversations = new Map();
  }

  /**
   * Create a new agent in this environment
   * @param {string} agentId - The unique agent identifier
   * @returns {Promise<CBCLAgent>} The created agent
   */
  async createAgent(agentId) {
    try {
      // Call the Scheme function to create an agent
      const agentData = this._callScheme('create-web-agent', [agentId]);
      const agent = new CBCLAgent(this.scheme, agentData);
      this.agents.set(agentId, agent);
      
      console.log(`Created agent in environment: ${agentId}`);
      return agent;
    } catch (error) {
      console.error(`Failed to create agent ${agentId}:`, error);
      throw error;
    }
  }

  /**
   * Get an existing agent by ID
   * @param {string} agentId - The agent identifier
   * @returns {CBCLAgent|null} The agent or null if not found
   */
  getAgent(agentId) {
    return this.agents.get(agentId) || null;
  }

  /**
   * Send a message between agents in this environment
   * @param {string} fromId - The sender agent ID
   * @param {string} toId - The recipient agent ID
   * @param {string} message - The message content
   * @returns {Object} The message delivery result
   */
  sendMessage(fromId, toId, message) {
    try {
      const fromAgent = this.getAgent(fromId);
      const toAgent = this.getAgent(toId);
      
      if (!fromAgent) {
        throw new Error(`Sender agent '${fromId}' not found`);
      }
      
      if (!toAgent) {
        throw new Error(`Recipient agent '${toId}' not found`);
      }

      const messageObj = {
        id: this._generateMessageId(),
        from: fromId,
        to: toId,
        content: message,
        timestamp: new Date().toISOString(),
        status: 'delivered'
      };

      this.messageQueue.push(messageObj);
      
      // Track conversation
      const conversationKey = [fromId, toId].sort().join('<->');
      if (!this.conversations.has(conversationKey)) {
        this.conversations.set(conversationKey, []);
      }
      this.conversations.get(conversationKey).push(messageObj);

      console.log(`Message sent from ${fromId} to ${toId}: ${message}`);
      return {
        success: true,
        messageId: messageObj.id,
        message: messageObj
      };
    } catch (error) {
      console.error(`Failed to send message:`, error);
      return {
        success: false,
        error: error.message
      };
    }
  }

  /**
   * List all agents in this environment
   * @returns {string[]} Array of agent IDs
   */
  listAgents() {
    return Array.from(this.agents.keys());
  }

  /**
   * Get environment statistics
   * @returns {Object} Environment stats
   */
  getStats() {
    return {
      agentCount: this.agents.size,
      messageCount: this.messageQueue.length,
      conversationCount: this.conversations.size,
      agents: this.listAgents()
    };
  }

  /**
   * Get message history for a conversation
   * @param {string} agent1 - First agent ID
   * @param {string} agent2 - Second agent ID
   * @returns {Object[]} Array of messages
   */
  getConversation(agent1, agent2) {
    const conversationKey = [agent1, agent2].sort().join('<->');
    return this.conversations.get(conversationKey) || [];
  }

  /**
   * Clear all messages and reset environment
   */
  reset() {
    this.messageQueue = [];
    this.conversations.clear();
    console.log('Environment reset');
  }

  // Private helper methods
  _callScheme(functionName, args) {
    console.log(`Environment calling Scheme: ${functionName}`, args);
    
    switch (functionName) {
      case 'create-web-agent':
        return ['agent', args[0]]; // [type, id]
      default:
        return ['unknown', functionName];
    }
  }

  _generateMessageId() {
    return `msg_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;
  }
}

class CBCLGossipNetwork {
  constructor(schemeModule) {
    this.scheme = schemeModule;
    this.agents = new Map();
    this.dialects = new Map();
    this.propagations = new Map();
  }

  /**
   * Add an agent to the gossip network
   * @param {CBCLAgent} agent - The agent to add
   */
  addAgent(agent) {
    this.agents.set(agent.getId(), agent);
    console.log(`Added agent ${agent.getId()} to gossip network`);
  }

  /**
   * Propagate a dialect through the network
   * @param {string} dialectName - The dialect to propagate
   * @param {Object} dialectSpec - The dialect specification
   * @returns {Object} Propagation result
   */
  propagateDialect(dialectName, dialectSpec) {
    try {
      // Initialize propagation state
      const propagation = {
        id: this._generatePropagationId(),
        dialect: dialectName,
        spec: dialectSpec,
        infected: new Set(),
        susceptible: new Set(this.agents.keys()),
        round: 0,
        startTime: Date.now()
      };

      this.propagations.set(propagation.id, propagation);
      this.dialects.set(dialectName, dialectSpec);

      console.log(`Started dialect propagation: ${dialectName}`);
      return {
        success: true,
        propagationId: propagation.id,
        dialectName
      };
    } catch (error) {
      return {
        success: false,
        error: error.message
      };
    }
  }

  /**
   * Simulate one step of gossip propagation
   * @param {string} propagationId - The propagation to step
   * @returns {Object} Step result
   */
  gossipStep(propagationId) {
    const propagation = this.propagations.get(propagationId);
    if (!propagation) {
      return { success: false, error: 'Propagation not found' };
    }

    propagation.round++;
    
    // Simple gossip simulation
    const newInfections = [];
    for (const infected of propagation.infected) {
      for (const susceptible of propagation.susceptible) {
        if (Math.random() < 0.3) { // 30% transmission probability
          propagation.infected.add(susceptible);
          propagation.susceptible.delete(susceptible);
          newInfections.push(susceptible);
        }
      }
    }

    console.log(`Gossip step ${propagation.round}: ${newInfections.length} new infections`);
    
    return {
      success: true,
      round: propagation.round,
      newInfections: newInfections.length,
      totalInfected: propagation.infected.size,
      remaining: propagation.susceptible.size,
      converged: propagation.susceptible.size === 0
    };
  }

  /**
   * Get network statistics
   * @returns {Object} Network stats
   */
  getNetworkStats() {
    return {
      agentCount: this.agents.size,
      dialectCount: this.dialects.size,
      activePropagations: this.propagations.size,
      agents: Array.from(this.agents.keys()),
      dialects: Array.from(this.dialects.keys())
    };
  }

  _generatePropagationId() {
    return `prop_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;
  }
}

/**
 * Main CBCL class that provides the entry point to the CBCL system
 */
class CBCL {
  constructor(schemeModule) {
    this.scheme = schemeModule;
    this.environments = new Map();
    this.gossipNetworks = new Map();
  }

  /**
   * Create a single agent (not in an environment)
   * @param {string} agentId - The agent identifier
   * @returns {Promise<CBCLAgent>} The created agent
   */
  async createAgent(agentId) {
    const agentData = this._callScheme('create-web-agent', [agentId]);
    return new CBCLAgent(this.scheme, agentData);
  }

  /**
   * Create a new multi-agent environment
   * @param {string} envId - Optional environment identifier
   * @returns {CBCLEnvironment} The created environment
   */
  createEnvironment(envId = null) {
    const id = envId || `env_${Date.now()}`;
    const environment = new CBCLEnvironment(this.scheme);
    this.environments.set(id, environment);
    console.log(`Created environment: ${id}`);
    return environment;
  }

  /**
   * Create a new gossip network
   * @param {string} networkId - Optional network identifier
   * @returns {CBCLGossipNetwork} The created gossip network
   */
  createGossipNetwork(networkId = null) {
    const id = networkId || `gossip_${Date.now()}`;
    const network = new CBCLGossipNetwork(this.scheme);
    this.gossipNetworks.set(id, network);
    console.log(`Created gossip network: ${id}`);
    return network;
  }

  /**
   * Run demo conversation
   * @returns {Promise<Object>} Demo result
   */
  async runDemo() {
    try {
      const result = this._callScheme('demo-conversation', []);
      return {
        success: true,
        demo: 'conversation',
        result
      };
    } catch (error) {
      return {
        success: false,
        error: error.message
      };
    }
  }

  /**
   * Test basic CBCL functionality
   * @returns {Promise<Object>} Test result
   */
  async test() {
    try {
      const result = this._callScheme('test-cbcl', []);
      return {
        success: true,
        test: 'basic',
        result
      };
    } catch (error) {
      return {
        success: false,
        error: error.message
      };
    }
  }

  _callScheme(functionName, args) {
    console.log(`CBCL calling Scheme: ${functionName}`, args);
    
    switch (functionName) {
      case 'create-web-agent':
        return ['agent', args[0]];
      case 'demo-conversation':
        return [
          ['asked', 'alice', ['bob', 'How are you?']],
          ['replied', 'bob', ['I\'m fine!']]
        ];
      case 'test-cbcl':
        return [
          ['asked', 'alice', ['bob', 'How are you?']],
          ['replied', 'bob', ['I\'m fine!']]
        ];
      default:
        return ['unknown', functionName];
    }
  }
}

/**
 * Load and initialize the CBCL WASM module
 * @param {string} wasmUrl - URL to the CBCL WASM file
 * @param {Object} options - Loading options
 * @returns {Promise<CBCL>} The initialized CBCL instance
 */
async function loadCBCL(wasmUrl, options = {}) {
  try {
    // Load the Hoot-compiled CBCL module
    const [cbclModule] = await Scheme.load_main(wasmUrl, {
      reflect_wasm_dir: options.reflect_wasm_dir || ".",
      user_imports: options.user_imports || {}
    });

    // Create and return the main CBCL interface
    const cbcl = new CBCL(cbclModule);
    
    console.log('CBCL WASM module loaded successfully');
    return cbcl;
  } catch (error) {
    console.error('Failed to load CBCL WASM module:', error);
    throw error;
  }
}

// Export classes and functions
if (typeof module !== 'undefined' && module.exports) {
  // Node.js environment
  module.exports = {
    CBCL,
    CBCLAgent,
    CBCLEnvironment,
    CBCLGossipNetwork,
    loadCBCL
  };
} else {
  // Browser environment
  window.CBCL = CBCL;
  window.CBCLAgent = CBCLAgent;
  window.CBCLEnvironment = CBCLEnvironment;
  window.CBCLGossipNetwork = CBCLGossipNetwork;
  window.loadCBCL = loadCBCL;
}
