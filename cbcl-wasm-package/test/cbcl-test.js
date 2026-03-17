/**
 * CBCL WASM Package Test Suite
 * 
 * Comprehensive tests for the CBCL WebAssembly package
 */

// Mock Scheme object for testing
const mockScheme = {
  load_main: async (wasmUrl, options) => {
    console.log(`Mock loading WASM from: ${wasmUrl}`);
    return [mockSchemeModule];
  }
};

const mockSchemeModule = {
  // Mock Scheme module for testing
  call: (functionName, ...args) => {
    console.log(`Mock Scheme call: ${functionName}`, args);
    return ['mock-result', functionName, args];
  }
};

// Set up global Scheme mock
global.Scheme = mockScheme;

// Import the CBCL module
const { CBCL, CBCLAgent, CBCLEnvironment, CBCLGossipNetwork, loadCBCL } = require('../src/cbcl-wasm.js');

/**
 * Test framework - simple assertion library
 */
class TestFramework {
  constructor() {
    this.tests = [];
    this.passed = 0;
    this.failed = 0;
  }

  test(description, testFunction) {
    this.tests.push({ description, testFunction });
  }

  assert(condition, message) {
    if (condition) {
      console.log(`✓ ${message}`);
      this.passed++;
    } else {
      console.error(`✗ ${message}`);
      this.failed++;
      throw new Error(`Assertion failed: ${message}`);
    }
  }

  assertEqual(actual, expected, message) {
    const condition = JSON.stringify(actual) === JSON.stringify(expected);
    this.assert(condition, `${message} (expected: ${JSON.stringify(expected)}, got: ${JSON.stringify(actual)})`);
  }

  assertTrue(condition, message) {
    this.assert(condition === true, message);
  }

  assertFalse(condition, message) {
    this.assert(condition === false, message);
  }

  async run() {
    console.log(`\n🧪 Running ${this.tests.length} tests...\n`);

    for (const { description, testFunction } of this.tests) {
      try {
        console.log(`📋 ${description}`);
        await testFunction();
        console.log('');
      } catch (error) {
        console.error(`❌ Test failed: ${error.message}\n`);
      }
    }

    console.log(`\n📊 Test Results:`);
    console.log(`✓ Passed: ${this.passed}`);
    console.log(`✗ Failed: ${this.failed}`);
    console.log(`📈 Success Rate: ${((this.passed / (this.passed + this.failed)) * 100).toFixed(1)}%`);

    return this.failed === 0;
  }
}

const test = new TestFramework();

// Test Suite
test.test('loadCBCL should initialize CBCL instance', async () => {
  const cbcl = await loadCBCL('mock.wasm');
  test.assertTrue(cbcl instanceof CBCL, 'Should return CBCL instance');
});

test.test('CBCL should create individual agents', async () => {
  const cbcl = await loadCBCL('mock.wasm');
  const agent = await cbcl.createAgent('alice');
  
  test.assertTrue(agent instanceof CBCLAgent, 'Should return CBCLAgent instance');
  test.assertEqual(agent.getId(), 'alice', 'Agent should have correct ID');
});

test.test('CBCL should create environments', async () => {
  const cbcl = await loadCBCL('mock.wasm');
  const env = cbcl.createEnvironment('test-env');
  
  test.assertTrue(env instanceof CBCLEnvironment, 'Should return CBCLEnvironment instance');
  test.assertEqual(env.listAgents().length, 0, 'New environment should be empty');
});

test.test('CBCLEnvironment should create agents', async () => {
  const cbcl = await loadCBCL('mock.wasm');
  const env = cbcl.createEnvironment();
  const agent = await env.createAgent('bob');
  
  test.assertTrue(agent instanceof CBCLAgent, 'Should return CBCLAgent instance');
  test.assertEqual(agent.getId(), 'bob', 'Agent should have correct ID');
  test.assertTrue(env.listAgents().includes('bob'), 'Environment should list the agent');
});

test.test('CBCLAgent should send tell messages', async () => {
  const cbcl = await loadCBCL('mock.wasm');
  const agent = await cbcl.createAgent('alice');
  const result = agent.tell('bob', 'Hello Bob!');
  
  test.assertTrue(result.success, 'Tell message should succeed');
  test.assertEqual(result.operation, 'tell', 'Should be tell operation');
  test.assertEqual(result.data.recipient, 'bob', 'Should have correct recipient');
  test.assertEqual(result.data.content, 'Hello Bob!', 'Should have correct content');
});

test.test('CBCLAgent should send ask messages', async () => {
  const cbcl = await loadCBCL('mock.wasm');
  const agent = await cbcl.createAgent('alice');
  const result = agent.ask('bob', 'How are you?');
  
  test.assertTrue(result.success, 'Ask message should succeed');
  test.assertEqual(result.operation, 'ask', 'Should be ask operation');
  test.assertEqual(result.data.recipient, 'bob', 'Should have correct recipient');
  test.assertEqual(result.data.query, 'How are you?', 'Should have correct query');
});

test.test('CBCLAgent should send reply messages', async () => {
  const cbcl = await loadCBCL('mock.wasm');
  const agent = await cbcl.createAgent('alice');
  const result = agent.reply('I am fine, thank you!');
  
  test.assertTrue(result.success, 'Reply message should succeed');
  test.assertEqual(result.operation, 'reply', 'Should be reply operation');
  test.assertEqual(result.data.content, 'I am fine, thank you!', 'Should have correct content');
});

test.test('CBCLAgent should parse simple tell messages', async () => {
  const cbcl = await loadCBCL('mock.wasm');
  const agent = await cbcl.createAgent('alice');
  const result = agent.parseMessage('(tell bob "Hello World")');
  
  test.assertTrue(result.success, 'Parse should succeed');
  test.assertEqual(result.operation, 'parse', 'Should be parse operation');
  test.assertEqual(result.data.parsed.type, 'tell', 'Should parse as tell message');
  test.assertEqual(result.data.parsed.recipient, 'bob', 'Should have correct recipient');
  test.assertEqual(result.data.parsed.content, 'Hello World', 'Should have correct content');
});

test.test('CBCLAgent should parse simple ask messages', async () => {
  const cbcl = await loadCBCL('mock.wasm');
  const agent = await cbcl.createAgent('alice');
  const result = agent.parseMessage('(ask charlie "What time is it?")');
  
  test.assertTrue(result.success, 'Parse should succeed');
  test.assertEqual(result.data.parsed.type, 'ask', 'Should parse as ask message');
  test.assertEqual(result.data.parsed.recipient, 'charlie', 'Should have correct recipient');
  test.assertEqual(result.data.parsed.query, 'What time is it?', 'Should have correct query');
});

test.test('CBCLAgent should parse simple reply messages', async () => {
  const cbcl = await loadCBCL('mock.wasm');
  const agent = await cbcl.createAgent('alice');
  const result = agent.parseMessage('(reply "It is 3:30 PM")');
  
  test.assertTrue(result.success, 'Parse should succeed');
  test.assertEqual(result.data.parsed.type, 'reply', 'Should parse as reply message');
  test.assertEqual(result.data.parsed.content, 'It is 3:30 PM', 'Should have correct content');
});

test.test('CBCLAgent should evaluate parsed messages', async () => {
  const cbcl = await loadCBCL('mock.wasm');
  const agent = await cbcl.createAgent('alice');
  const parsed = { type: 'tell', recipient: 'bob', content: 'Hello' };
  const result = agent.evaluateMessage(parsed);
  
  test.assertTrue(result.success, 'Evaluation should succeed');
  test.assertEqual(result.operation, 'evaluate', 'Should be evaluate operation');
});

test.test('CBCLEnvironment should send messages between agents', async () => {
  const cbcl = await loadCBCL('mock.wasm');
  const env = cbcl.createEnvironment();
  
  await env.createAgent('alice');
  await env.createAgent('bob');
  
  const result = env.sendMessage('alice', 'bob', 'Hello Bob!');
  
  test.assertTrue(result.success, 'Message sending should succeed');
  test.assertEqual(result.message.from, 'alice', 'Should have correct sender');
  test.assertEqual(result.message.to, 'bob', 'Should have correct recipient');
  test.assertEqual(result.message.content, 'Hello Bob!', 'Should have correct content');
});

test.test('CBCLEnvironment should track conversations', async () => {
  const cbcl = await loadCBCL('mock.wasm');
  const env = cbcl.createEnvironment();
  
  await env.createAgent('alice');
  await env.createAgent('bob');
  
  env.sendMessage('alice', 'bob', 'Hello!');
  env.sendMessage('bob', 'alice', 'Hi there!');
  
  const conversation = env.getConversation('alice', 'bob');
  test.assertEqual(conversation.length, 2, 'Should track both messages');
});

test.test('CBCLEnvironment should provide statistics', async () => {
  const cbcl = await loadCBCL('mock.wasm');
  const env = cbcl.createEnvironment();
  
  await env.createAgent('alice');
  await env.createAgent('bob');
  env.sendMessage('alice', 'bob', 'Test message');
  
  const stats = env.getStats();
  test.assertEqual(stats.agentCount, 2, 'Should count agents correctly');
  test.assertEqual(stats.messageCount, 1, 'Should count messages correctly');
  test.assertTrue(stats.agents.includes('alice'), 'Should list alice');
  test.assertTrue(stats.agents.includes('bob'), 'Should list bob');
});

test.test('CBCL should create gossip networks', async () => {
  const cbcl = await loadCBCL('mock.wasm');
  const network = cbcl.createGossipNetwork('test-network');
  
  test.assertTrue(network instanceof CBCLGossipNetwork, 'Should return CBCLGossipNetwork instance');
});

test.test('CBCLGossipNetwork should add agents and propagate dialects', async () => {
  const cbcl = await loadCBCL('mock.wasm');
  const network = cbcl.createGossipNetwork();
  const agent1 = await cbcl.createAgent('agent1');
  const agent2 = await cbcl.createAgent('agent2');
  
  network.addAgent(agent1);
  network.addAgent(agent2);
  
  const dialectSpec = { name: 'test-dialect', performatives: ['greet', 'farewell'] };
  const result = network.propagateDialect('test-dialect', dialectSpec);
  
  test.assertTrue(result.success, 'Dialect propagation should succeed');
  test.assertEqual(result.dialectName, 'test-dialect', 'Should have correct dialect name');
});

test.test('CBCLGossipNetwork should simulate gossip steps', async () => {
  const cbcl = await loadCBCL('mock.wasm');
  const network = cbcl.createGossipNetwork();
  
  // Add some agents
  for (let i = 0; i < 5; i++) {
    const agent = await cbcl.createAgent(`agent${i}`);
    network.addAgent(agent);
  }
  
  const dialectSpec = { name: 'test-dialect' };
  const propagation = network.propagateDialect('test-dialect', dialectSpec);
  const step = network.gossipStep(propagation.propagationId);
  
  test.assertTrue(step.success, 'Gossip step should succeed');
  test.assertTrue(step.round >= 1, 'Should increment round number');
});

test.test('CBCL should run demo conversations', async () => {
  const cbcl = await loadCBCL('mock.wasm');
  const result = await cbcl.runDemo();
  
  test.assertTrue(result.success, 'Demo should succeed');
  test.assertEqual(result.demo, 'conversation', 'Should be conversation demo');
});

test.test('CBCL should run basic tests', async () => {
  const cbcl = await loadCBCL('mock.wasm');
  const result = await cbcl.test();
  
  test.assertTrue(result.success, 'Basic test should succeed');
  test.assertEqual(result.test, 'basic', 'Should be basic test');
});

// Performance tests
test.test('Performance: Should handle multiple agents efficiently', async () => {
  const cbcl = await loadCBCL('mock.wasm');
  const env = cbcl.createEnvironment();
  
  const startTime = Date.now();
  
  // Create 100 agents
  for (let i = 0; i < 100; i++) {
    await env.createAgent(`agent${i}`);
  }
  
  const creationTime = Date.now() - startTime;
  console.log(`Created 100 agents in ${creationTime}ms`);
  
  test.assertTrue(creationTime < 5000, 'Should create 100 agents in under 5 seconds');
  test.assertEqual(env.listAgents().length, 100, 'Should have 100 agents');
});

test.test('Performance: Should handle message passing efficiently', async () => {
  const cbcl = await loadCBCL('mock.wasm');
  const env = cbcl.createEnvironment();
  
  await env.createAgent('sender');
  await env.createAgent('receiver');
  
  const startTime = Date.now();
  
  // Send 1000 messages
  for (let i = 0; i < 1000; i++) {
    env.sendMessage('sender', 'receiver', `Message ${i}`);
  }
  
  const messagingTime = Date.now() - startTime;
  console.log(`Sent 1000 messages in ${messagingTime}ms`);
  
  test.assertTrue(messagingTime < 5000, 'Should send 1000 messages in under 5 seconds');
  test.assertEqual(env.getStats().messageCount, 1000, 'Should have 1000 messages');
});

// Error handling tests
test.test('Error handling: Should handle invalid agent IDs gracefully', async () => {
  const cbcl = await loadCBCL('mock.wasm');
  const env = cbcl.createEnvironment();
  
  const result = env.sendMessage('nonexistent', 'alsononexistent', 'test');
  test.assertFalse(result.success, 'Should fail for nonexistent agents');
  test.assertTrue(result.error.includes('not found'), 'Should have appropriate error message');
});

test.test('Error handling: Should handle malformed messages gracefully', async () => {
  const cbcl = await loadCBCL('mock.wasm');
  const agent = await cbcl.createAgent('alice');
  
  const result = agent.parseMessage('not a valid message');
  test.assertTrue(result.success, 'Parse should succeed even for malformed messages');
  test.assertEqual(result.data.parsed.type, 'unknown', 'Should mark as unknown type');
});

// Integration tests
test.test('Integration: Complete conversation workflow', async () => {
  const cbcl = await loadCBCL('mock.wasm');
  const env = cbcl.createEnvironment();
  
  const alice = await env.createAgent('alice');
  const bob = await env.createAgent('bob');
  
  // Alice asks Bob a question
  const askResult = alice.ask('bob', 'How are you today?');
  test.assertTrue(askResult.success, 'Ask should succeed');
  
  // Bob replies
  const replyResult = bob.reply('I am doing great, thanks for asking!');
  test.assertTrue(replyResult.success, 'Reply should succeed');
  
  // Check environment message tracking
  const deliveryResult = env.sendMessage('alice', 'bob', askResult.data.query);
  test.assertTrue(deliveryResult.success, 'Message delivery should succeed');
  
  const conversation = env.getConversation('alice', 'bob');
  test.assertTrue(conversation.length > 0, 'Should have conversation history');
});

// Run all tests
if (require.main === module) {
  test.run().then(success => {
    process.exit(success ? 0 : 1);
  });
}

module.exports = { test, TestFramework };
