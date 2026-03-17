#!/usr/bin/env node

/**
 * CBCL WASM Package Demonstration
 * 
 * This script demonstrates the full functionality of the CBCL WASM package
 * including agent creation, messaging, environments, and gossip networks.
 */

const { CBCL, CBCLAgent, CBCLEnvironment, CBCLGossipNetwork, loadCBCL } = require('./src/cbcl-wasm.js');

// Mock Scheme for Node.js demo
global.Scheme = {
  load_main: async (wasmUrl, options) => {
    console.log(`🔧 Mock loading WASM from: ${wasmUrl}`);
    return [{ call: () => 'mock-result' }];
  }
};

async function runDemo() {
  console.log('🚀 CBCL WASM Package Demonstration');
  console.log('=====================================\n');

  try {
    // 1. Load CBCL
    console.log('📦 1. Loading CBCL WASM module...');
    const cbcl = await loadCBCL('mock.wasm');
    console.log('✅ CBCL module loaded successfully!\n');

    // 2. Create agents
    console.log('🤖 2. Creating individual agents...');
    const alice = await cbcl.createAgent('alice');
    const bob = await cbcl.createAgent('bob');
    console.log(`✅ Created agents: ${alice.getId()}, ${bob.getId()}\n`);

    // 3. Demonstrate messaging
    console.log('💬 3. Demonstrating message passing...');
    
    const tellResult = alice.tell('bob', 'Hello Bob! How are you today?');
    console.log(`📤 Alice tells Bob: ${JSON.stringify(tellResult.data)}`);
    
    const askResult = bob.ask('alice', 'What are you working on?');
    console.log(`❓ Bob asks Alice: ${JSON.stringify(askResult.data)}`);
    
    const replyResult = alice.reply('I am working on CBCL!');
    console.log(`💬 Alice replies: ${JSON.stringify(replyResult.data)}\n`);

    // 4. Create environment
    console.log('🌐 4. Creating multi-agent environment...');
    const env = cbcl.createEnvironment('demo-environment');
    
    const envAlice = await env.createAgent('env-alice');
    const envBob = await env.createAgent('env-bob');
    const envCharlie = await env.createAgent('env-charlie');
    
    console.log(`✅ Environment created with agents: ${env.listAgents().join(', ')}\n`);

    // 5. Environment messaging
    console.log('📨 5. Demonstrating environment messaging...');
    
    env.sendMessage('env-alice', 'env-bob', 'Hello from environment!');
    env.sendMessage('env-bob', 'env-alice', 'Hi Alice! Great to be here.');
    env.sendMessage('env-charlie', 'env-alice', 'Hey everyone! This is Charlie.');
    
    const stats = env.getStats();
    console.log(`📊 Environment stats: ${JSON.stringify(stats)}`);
    
    const conversation = env.getConversation('env-alice', 'env-bob');
    console.log(`💬 Alice-Bob conversation: ${conversation.length} messages\n`);

    // 6. Message parsing
    console.log('📝 6. Demonstrating message parsing...');
    
    const messages = [
      '(tell bob "Hello World")',
      '(ask charlie "What time is it?")',
      '(reply "It is 3:30 PM")'
    ];
    
    for (const msg of messages) {
      const parsed = alice.parseMessage(msg);
      console.log(`📋 "${msg}" → Type: ${parsed.data.parsed.type}`);
    }
    console.log();

    // 7. Gossip network
    console.log('🗣️ 7. Creating gossip network...');
    const network = cbcl.createGossipNetwork('demo-gossip');
    
    // Add agents to network
    const gossipAgents = [];
    for (let i = 0; i < 5; i++) {
      const agent = await cbcl.createAgent(`gossip-agent-${i}`);
      network.addAgent(agent);
      gossipAgents.push(agent);
    }
    
    console.log(`✅ Added ${gossipAgents.length} agents to gossip network`);

    // 8. Dialect propagation
    console.log('🌐 8. Demonstrating dialect propagation...');
    
    const dialectSpec = {
      name: 'demo-dialect',
      performatives: ['greet', 'farewell', 'acknowledge'],
      examples: [
        '(greet alice "Good morning!")',
        '(farewell bob "See you later!")',
        '(acknowledge charlie "Message received")'
      ]
    };
    
    const propagation = network.propagateDialect('demo-dialect', dialectSpec);
    console.log(`🚀 Started propagation: ${propagation.dialectName}`);
    
    // Simulate gossip steps
    console.log('📡 Simulating gossip propagation...');
    for (let step = 0; step < 3; step++) {
      const result = network.gossipStep(propagation.propagationId);
      console.log(`   Round ${result.round}: ${result.newInfections} new infections, ${result.totalInfected} total infected`);
      
      if (result.converged) {
        console.log('🎉 Dialect fully propagated!');
        break;
      }
    }
    
    const networkStats = network.getNetworkStats();
    console.log(`📊 Network stats: ${JSON.stringify(networkStats)}\n`);

    // 9. Demo and test functions
    console.log('🧪 9. Running built-in demos and tests...');
    
    const demoResult = await cbcl.runDemo();
    console.log(`🎭 Demo conversation result: ${JSON.stringify(demoResult)}`);
    
    const testResult = await cbcl.test();
    console.log(`🧪 Basic test result: ${JSON.stringify(testResult)}\n`);

    // 10. Performance demonstration
    console.log('⚡ 10. Performance demonstration...');
    
    const perfEnv = cbcl.createEnvironment('perf-env');
    const startTime = Date.now();
    
    // Create many agents quickly
    for (let i = 0; i < 50; i++) {
      await perfEnv.createAgent(`perf-agent-${i}`);
    }
    
    const agentCreationTime = Date.now() - startTime;
    console.log(`⚡ Created 50 agents in ${agentCreationTime}ms`);
    
    // Send many messages quickly
    await perfEnv.createAgent('sender');
    await perfEnv.createAgent('receiver');
    
    const msgStartTime = Date.now();
    for (let i = 0; i < 100; i++) {
      perfEnv.sendMessage('sender', 'receiver', `Performance test message ${i}`);
    }
    const msgTime = Date.now() - msgStartTime;
    console.log(`⚡ Sent 100 messages in ${msgTime}ms`);
    
    const perfStats = perfEnv.getStats();
    console.log(`📊 Performance environment final stats: ${JSON.stringify(perfStats)}\n`);

    console.log('🎉 CBCL WASM Package Demonstration Complete!');
    console.log('=============================================');
    console.log('');
    console.log('📋 Features Demonstrated:');
    console.log('  ✅ Agent creation and management');
    console.log('  ✅ Message passing (tell, ask, reply)');
    console.log('  ✅ Multi-agent environments');
    console.log('  ✅ Message parsing and evaluation');
    console.log('  ✅ Gossip networks and dialect propagation');
    console.log('  ✅ Built-in demos and tests');
    console.log('  ✅ Performance optimization');
    console.log('');
    console.log('🚀 Ready for production use!');

  } catch (error) {
    console.error('❌ Demo failed:', error.message);
    console.error(error.stack);
    process.exit(1);
  }
}

// Run the demo
if (require.main === module) {
  runDemo();
}

module.exports = { runDemo };
