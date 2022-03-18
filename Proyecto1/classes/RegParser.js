const { performance } = require('universal-perf-hooks');

const FSM = require('./FSM');
const NFA = require('./NFA');
const NFAState = require('./NFAState');
const { convertToBasicOperators } = require('../utils');
const { EPSILONTOKEN } = require('./Lexer');
const { Lexer } = require('./Lexer');
const { TOKEN_TYPE } = require('./Lexer');

class RegParser {
  constructor(regString) {
    const regExpBasic = convertToBasicOperators(regString);
    this.nfa = null;
    this.id = 0;
    this.lexer = new Lexer(regExpBasic);
    this.lookHead = this.lexer.nextToken();
  }

  clear() {
    this.nfa = null;
    this.id = 0;
    this.lexer = null;
    this.lookHead = null;
  }

  reset(regString) {
    const regExpBasic = convertToBasicOperators(regString);
    this.nfa = null;
    this.id = 0;
    this.lexer = new Lexer(regExpBasic);
    this.lookHead = this.lexer.nextToken();
  }

  parseToNFA() {
    const beginTime = performance.now();
    this.nfa = this._expression();
    this._reorderNFAStateId();
    const fsm = this._traversalFSM();
    const executionTime = performance.now() - beginTime;
    return {
      fsm,
      nfa: this.nfa,
      executionTime,
    };
  }

  parseToDFA() {
    this.parseToNFA();
    return this.nfa.toDFA();
  }

  _traversalFSM() {
    const fsm = new FSM();
    const queue = [];
    const vis = {};
    queue.push(this.nfa.startState);

    fsm.initialState = this.nfa.startState.id.toString();
    fsm.numOfStates = this.id;
    fsm.type = 'NFA';
    vis[this.nfa.startState.id] = 1;
    while (queue.length) {
      const state = queue.shift();
      for (let i = 0; i < (state.nextStates).length; ++i) {
        const nextId = state.nextStates[i][1].id;
        const label = state.nextStates[i][0].text;
        const nextState = state.nextStates[i][1];
        if (!fsm.transitions[state.id]) {
          fsm.transitions[state.id] = {};
        }

        fsm.transitions[state.id][nextId] = label;
        if (nextId in vis) {
          continue;
        }

        vis[nextId] = 1;
        if (nextState.isAccept) {
          fsm.acceptStates.push(nextId.toString());
        }

        queue.push(state.nextStates[i][1]);
      }
    }
    return fsm;
  }

  _reorderNFAStateId() {
    const queue = [];
    const ordered = [];
    const vis = {};
    queue.push(this.nfa.startState);
    this.id = 0;
    vis[this.nfa.startState.id] = 1;
    while (queue.length) {
      const state = queue.shift();
      ordered.push(state);
      for (let i = 0; i < (state.nextStates).length; ++i) {
        const nextId = state.nextStates[i][1].id;
        if (nextId in vis) { continue; }
        vis[nextId] = 1;
        queue.push(state.nextStates[i][1]);
      }
    }
    while (ordered.length) {
      const state = ordered.shift();
      state.id = this.id++;
    }
  }

  _expression() {
    const expressionNFA = this._expressionWithoutOr();
    if (this.lookHead.type === TOKEN_TYPE.OR) {
      this._match(TOKEN_TYPE.OR);
      return this._combineNFAsForOR(expressionNFA, this._expression());
    }
    return expressionNFA;
  }

  _expressionWithoutOr() {
    const factorNFA = this._factor();
    if (this.lookHead.type === TOKEN_TYPE.REGCHAR
      || this.lookHead.type === TOKEN_TYPE.LBRACK) {
      const subNFA = this._expressionWithoutOr();
      factorNFA.endState.isAccept = false;
      factorNFA.endState.id = subNFA.startState.id;
      factorNFA.endState.nextStates = subNFA.startState.nextStates;
      subNFA.startState = null;

      return new NFA(factorNFA.startState, subNFA.endState);
    }
    return factorNFA;
  }

  _factor() {
    const termNFA = this._term();
    if (this.lookHead.type === TOKEN_TYPE.STAR) { // case *
      const nfa = new NFA(new NFAState(this.id++, false),
        new NFAState(this.id++, true));
      termNFA.endState.isAccept = false;

      nfa.startState.addStates(EPSILONTOKEN, termNFA.startState);
      nfa.startState.addStates(EPSILONTOKEN, nfa.endState);
      termNFA.endState.addStates(EPSILONTOKEN, nfa.endState);
      termNFA.endState.addStates(EPSILONTOKEN, termNFA.startState);

      this._match(TOKEN_TYPE.STAR);
      return nfa;
    } if (this.lookHead.type === TOKEN_TYPE.Unknown) {
      throw new Error(`Unknown symbol: ${this.lookHead.text}`);
    }
    return termNFA;
  }

  _term() {
    if (this.lookHead.type === TOKEN_TYPE.REGCHAR
      || this.lookHead.type === TOKEN_TYPE.EPSILON) {
      const nfa = new NFA(new NFAState(this.id++, false),
        new NFAState(this.id++, true));
      nfa.startState.addStates(this.lookHead, nfa.endState);
      this._match(this.lookHead.type);
      return nfa;
    } if (this.lookHead.type === TOKEN_TYPE.LBRACK) {
      this._match(TOKEN_TYPE.LBRACK);
      const nfa = this._expression();
      this._match(TOKEN_TYPE.RBRACK);
      return nfa;
    }
    throw new Error(`Invalid term: ${this.lookHead.text}`);
  }

  _match(type) {
    if (this.lookHead.type === type) {
      this._consume();
    } else {
      throw new Error(`Cannot match type: ${this.lookHead.text}`);
    }
  }

  _consume() {
    this.lookHead = this.lexer.nextToken();
  }

  _combineNFAsForOR(subNFA1, subNFA2) {
    const newNFA = new NFA(new NFAState(this.id++, false),
      new NFAState(this.id++, true));
    subNFA1.endState.isAccept = false;
    subNFA2.endState.isAccept = false;

    newNFA.startState.addStates(EPSILONTOKEN, subNFA1.startState);
    newNFA.startState.addStates(EPSILONTOKEN, subNFA2.startState);
    subNFA1.endState.addStates(EPSILONTOKEN, newNFA.endState);
    subNFA2.endState.addStates(EPSILONTOKEN, newNFA.endState);
    return newNFA;
  }
}

module.exports = RegParser;
