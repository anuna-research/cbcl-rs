/**
 * CBCL WebAssembly Package TypeScript Definitions
 * 
 * Type definitions for the CBCL (Chat-based Communication Language) 
 * WebAssembly package.
 */

export interface CBCLMessage {
  id?: string;
  type: 'tell' | 'ask' | 'reply' | 'unknown';
  performative?: string;
  params?: any[];
  timestamp?: string;
  from?: string;
  to?: string;
  content?: string;
  query?: string;
  recipient?: string;
  raw?: string;
}

export interface CBCLResult {
  success: boolean;
  operation: string;
  timestamp: string;
  agent: string;
  data?: any;
  error?: string;
}

export interface ParseResult extends CBCLResult {
  data: {
    message: string;
    parsed: CBCLMessage;
  };
}

export interface EvaluationResult extends CBCLResult {
  data: {
    message: CBCLMessage;
    result: any[];
  };
}

export interface MessageResult extends CBCLResult {
  data: {
    recipient: string;
    content: string;
    result: any[];
  };
}

export interface EnvironmentMessage {
  id: string;
  from: string;
  to: string;
  content: string;
  timestamp: string;
  status: string;
}

export interface EnvironmentStats {
  agentCount: number;
  messageCount: number;
  conversationCount: number;
  agents: string[];
}

export interface DialectSpec {
  name: string;
  performatives?: string[];
  examples?: string[];
  author?: string;
  signature?: string;
  hash?: string;
  protocol?: any;
  resources?: any;
  extends?: string[];
}

export interface PropagationResult {
  success: boolean;
  propagationId?: string;
  dialectName?: string;
  error?: string;
}

export interface GossipStepResult {
  success: boolean;
  round?: number;
  newInfections?: number;
  totalInfected?: number;
  remaining?: number;
  converged?: boolean;
  error?: string;
}

export interface NetworkStats {
  agentCount: number;
  dialectCount: number;
  activePropagations: number;
  agents: string[];
  dialects: string[];
}

export interface LoadOptions {
  reflect_wasm_dir?: string;
  user_imports?: Record<string, any>;
}

/**
 * Represents a CBCL agent capable of sending and receiving messages
 */
export declare class CBCLAgent {
  constructor(schemeModule: any, agentData: any);
  
  /**
   * Get the agent's unique identifier
   */
  getId(): string;
  
  /**
   * Send a tell message to another agent
   */
  tell(recipient: string, content: string): MessageResult;
  
  /**
   * Send an ask message to another agent
   */
  ask(recipient: string, query: string): MessageResult;
  
  /**
   * Send a reply message
   */
  reply(content: string): MessageResult;
  
  /**
   * Parse a CBCL message string
   */
  parseMessage(messageStr: string): ParseResult;
  
  /**
   * Evaluate a parsed message
   */
  evaluateMessage(message: CBCLMessage): EvaluationResult;
}

/**
 * Manages multiple agents and their interactions
 */
export declare class CBCLEnvironment {
  constructor(schemeModule: any);
  
  /**
   * Create a new agent in this environment
   */
  createAgent(agentId: string): Promise<CBCLAgent>;
  
  /**
   * Get an existing agent by ID
   */
  getAgent(agentId: string): CBCLAgent | null;
  
  /**
   * Send a message between agents in this environment
   */
  sendMessage(fromId: string, toId: string, message: string): {
    success: boolean;
    messageId?: string;
    message?: EnvironmentMessage;
    error?: string;
  };
  
  /**
   * List all agents in this environment
   */
  listAgents(): string[];
  
  /**
   * Get environment statistics
   */
  getStats(): EnvironmentStats;
  
  /**
   * Get message history for a conversation
   */
  getConversation(agent1: string, agent2: string): EnvironmentMessage[];
  
  /**
   * Clear all messages and reset environment
   */
  reset(): void;
}

/**
 * Implements epidemic dialect propagation
 */
export declare class CBCLGossipNetwork {
  constructor(schemeModule: any);
  
  /**
   * Add an agent to the gossip network
   */
  addAgent(agent: CBCLAgent): void;
  
  /**
   * Propagate a dialect through the network
   */
  propagateDialect(dialectName: string, dialectSpec: DialectSpec): PropagationResult;
  
  /**
   * Simulate one step of gossip propagation
   */
  gossipStep(propagationId: string): GossipStepResult;
  
  /**
   * Get network statistics
   */
  getNetworkStats(): NetworkStats;
}

/**
 * Main CBCL class that provides the entry point to the CBCL system
 */
export declare class CBCL {
  constructor(schemeModule: any);
  
  /**
   * Create a single agent (not in an environment)
   */
  createAgent(agentId: string): Promise<CBCLAgent>;
  
  /**
   * Create a new multi-agent environment
   */
  createEnvironment(envId?: string): CBCLEnvironment;
  
  /**
   * Create a new gossip network
   */
  createGossipNetwork(networkId?: string): CBCLGossipNetwork;
  
  /**
   * Run demo conversation
   */
  runDemo(): Promise<{
    success: boolean;
    demo?: string;
    result?: any;
    error?: string;
  }>;
  
  /**
   * Test basic CBCL functionality
   */
  test(): Promise<{
    success: boolean;
    test?: string;
    result?: any;
    error?: string;
  }>;
}

/**
 * Load and initialize the CBCL WASM module
 */
export declare function loadCBCL(wasmUrl: string, options?: LoadOptions): Promise<CBCL>;

// Global exports for browser usage
declare global {
  const CBCL: typeof CBCL;
  const CBCLAgent: typeof CBCLAgent;
  const CBCLEnvironment: typeof CBCLEnvironment;
  const CBCLGossipNetwork: typeof CBCLGossipNetwork;
  const loadCBCL: typeof loadCBCL;
  
  interface Window {
    CBCL: typeof CBCL;
    CBCLAgent: typeof CBCLAgent;
    CBCLEnvironment: typeof CBCLEnvironment;
    CBCLGossipNetwork: typeof CBCLGossipNetwork;
    loadCBCL: typeof loadCBCL;
  }
}
