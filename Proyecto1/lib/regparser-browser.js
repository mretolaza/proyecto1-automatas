require=(function e(t,n,r){function s(o,u){if(!n[o]){if(!t[o]){var a=typeof require=="function"&&require;if(!u&&a)return a(o,!0);if(i)return i(o,!0);var f=new Error("Cannot find module '"+o+"'");throw f.code="MODULE_NOT_FOUND",f}var l=n[o]={exports:{}};t[o][0].call(l.exports,function(e){var n=t[o][1][e];return s(n?n:e)},l,l.exports,e,t,n,r)}return n[o].exports}var i=typeof require=="function"&&require;for(var o=0;o<r.length;o++)s(r[o]);return s})({1:[function(require,module,exports){
const { concat } = require('lodash');

class DFANode {
  constructor(id, type, label, children = []) {
    this.id = id;
    this.type = type;
    this.label = label;
    this.children = children;
    this.nullable = false;
    this.left = {};
    this.right = {};
    this.firstPosition = [];
    this.lastPosition = [];
    // this.nextPosition = [];
  }

  addChildren(children) {
    this.children = concat(this.children, children);
  }
}

module.exports = DFANode;

},{"lodash":10}],2:[function(require,module,exports){
/* eslint-disable global-require */
/* eslint-disable no-case-declarations */
const {
  concat,
  orderBy,
  sortBy,
  uniq,
} = require('lodash');
const regexpTree = require('regexp-tree');
const { performance } = require('universal-perf-hooks');

const FSM = require('./FSM');
const DFANode = require('./DFANode');
const NFAState = require('./NFAState');
const { Token } = require('./Lexer');

const { TOKEN_TYPE, REG_TREE_TYPE, DFA_NODE_TYPE } = require('../constants');

const {
  calculatedFunctions,
  convertToBasicOperators,
} = require('../utils');

const _nextPosition = function (root, leafs) {
  const nodesToCheck = [];
  const nodes = [root];

  while (nodes.length) {
    const node = nodes.shift();
    node.children.forEach((child) => {
      nodes.push(child);
    });

    if ((node.label === 'CONCAT' && node.children.length > 1)
      || node.label === 'KLEEN') {
      nodesToCheck.push(node);
    }
  }

  nodesToCheck.forEach((node) => {
    if (node.label === 'KLEEN') {
      const { firstPosition, lastPosition } = node;
      for (let i = 0; i < lastPosition.length; ++i) {
        for (let j = 0; j < firstPosition.length; ++j) {
          if (leafs[lastPosition[i]].nextPosition.findIndex(
            (sigPos) => sigPos === firstPosition[j],
          ) === -1) {
            leafs[lastPosition[i]].nextPosition.push(firstPosition[j]);
          }
        }
        leafs[lastPosition[i]].nextPosition = sortBy(leafs[lastPosition[i]].nextPosition);
      }
    } else {
      node.children.forEach((child, index) => {
        if (index + 1 < node.children.length) {
          const nextChild = node.children[index + 1];
          const { lastPosition } = child;
          const { firstPosition } = nextChild;
          for (let i = 0; i < lastPosition.length; ++i) {
            for (let j = 0; j < firstPosition.length; ++j) {
              if (leafs[lastPosition[i]].nextPosition.findIndex(
                (sigPos) => sigPos === firstPosition[j],
              ) === -1) {
                leafs[lastPosition[i]].nextPosition.push(firstPosition[j]);
              }
            }
            leafs[lastPosition[i]].nextPosition = sortBy(leafs[lastPosition[i]].nextPosition);
          }
        }
      });
    }
  });

  return leafs;
};

const _toFSM = function (transitions) {
  const {
    stateId, dfa,
  } = transitions;

  const fsm = new FSM();
  fsm.type = 'DirectDFA';
  fsm.numOfStates = stateId;
  fsm.transitions = {};

  const stateStack = [dfa];

  while (stateStack.length) {
    const state = stateStack.shift();

    if (state.isInitial) {
      fsm.initialState = `S${state.id}`;
    }

    if (state.isAccept) {
      fsm.acceptStates.push(`S${state.id}`);
    }

    for (let i = 0; i < state.nextStates.length; ++i) {
      const [token, nextState] = state.nextStates[i];
      stateStack.push(nextState);

      if (!fsm.transitions[`S${state.id}`]) {
        fsm.transitions[`S${state.id}`] = {};
      }

      fsm.transitions[`S${state.id}`][token.text] = `S${nextState.id}`;
    }
  }

  return fsm;
};

// class Parser
class DirectDFA {
  constructor(regString) {
    const regExp = `(${convertToBasicOperators(regString)})#`;

    const parsed = regexpTree.parse(new RegExp(regExp));
    this.expressions = parsed.body.expressions || [parsed.body];
    this.leafs = {};
    this.alphabetTable = [];

    this.id = 1;
  }

  _group(group) {
    const { expression } = group;
    const node = new DFANode(
      0,
      DFA_NODE_TYPE.node,
      'GROUP',
    );
    let children = [];

    switch (expression.type) {
      case REG_TREE_TYPE.Group:
        children = this._group(expression);
        break;
      case REG_TREE_TYPE.Char:
        children = this._term(expression);
        break;
      case REG_TREE_TYPE.Alternative:
        children = this._expression(expression);
        break;
      case REG_TREE_TYPE.Or:
      case REG_TREE_TYPE.Kleen:
        children = this._expression({ expressions: concat(expression) });
        break;
      default:
        children = [];
        break;
    }

    node.addChildren(children);
    return node;
  }

  _expression({ expressions }, type = 'CONCAT') {
    let node = new DFANode(
      0,
      DFA_NODE_TYPE.node,
      type,
    );

    expressions.forEach((expression) => {
      let children = [];
      switch (expression.type) {
        case REG_TREE_TYPE.Group:
          children = this._group(expression);
          break;
        case REG_TREE_TYPE.Char:
          children = this._term(expression);
          break;
        case REG_TREE_TYPE.Alternative:
          children = this._expression(expression);
          break;
        case REG_TREE_TYPE.Or:
          node = new DFANode(
            0,
            DFA_NODE_TYPE.node,
            'OR',
          );

          node.left = this._expression({ expressions: concat(expression.left) });
          node.right = this._expression({ expressions: concat(expression.right) });

          node.addChildren(node.left);
          node.addChildren(node.right);
          break;
        case REG_TREE_TYPE.Kleen:
          children = this._expression({ expressions: concat(expression.expression) }, 'KLEEN');
          break;
        default:
          children = [];
      }

      node.addChildren(children);
    });

    return node;
  }

  _term(expression) {
    if (expression.value !== TOKEN_TYPE.EPSILON) {
      this.leafs[this.id] = {
        label: expression.value,
        nextPosition: [],
      };
    }

    if (this.alphabetTable.findIndex((letter) => letter === expression.value) === -1
      && expression.value !== DFA_NODE_TYPE.increased) {
      this.alphabetTable.push(expression.value);
    }

    return new DFANode(
      (expression.value !== TOKEN_TYPE.EPSILON) ? this.id++ : 0,
      DFA_NODE_TYPE.leaf,
      expression.value,
    );
  }

  _syntacticTree() {
    const node = new DFANode(
      0,
      DFA_NODE_TYPE.root,
      'CONCAT',
    );
    const childrenGroup = this._group(this.expressions[0]);
    const increasedChild = this._term(this.expressions[1]);

    node.addChildren(childrenGroup);
    node.addChildren(increasedChild);

    return node;
  }

  _transitionsTable(firstState, leafs) {
    const acceptLeafId = Object.keys(leafs)
      .map((key) => ({ id: key, label: leafs[key].label }))
      .find((leaf) => leaf.label === DFA_NODE_TYPE.increased).id;

    const isAcceptState = (nextPositions) => nextPositions.includes(+acceptLeafId);
    const getPositionId = (array) => JSON.stringify(array);

    let stateId = 0;
    const states = [];
    const stateStack = [];

    const dfa = new NFAState(
      stateId++,
      isAcceptState(firstState),
      true,
    );

    states.push({
      positionId: getPositionId(firstState),
      nextPosition: firstState,
      dfaState: dfa,
      transitions: [],
    });

    stateStack.push(states[0]);

    while (stateStack.length) {
      const state = stateStack.shift();

      // eslint-disable-next-line no-loop-func
      this.alphabetTable.forEach((letter) => {
        let nextPositions = [];
        state.nextPosition.forEach((position) => {
          if (leafs[position].label === letter) {
            nextPositions = uniq(concat(nextPositions, leafs[position].nextPosition));
          }
        });
        nextPositions = orderBy(nextPositions);

        if (nextPositions.length > 0) {
          const positionId = getPositionId(nextPositions);
          const stateIndex = states.findIndex((s) => s.positionId === positionId);
          if (stateIndex === -1) {
            const dfaState = new NFAState(stateId++, isAcceptState(nextPositions));
            const newState = {
              positionId: getPositionId(nextPositions),
              nextPosition: nextPositions,
              dfaState,
              transitions: [],
            };

            states.push(newState);
            stateStack.push(newState);

            state.dfaState.addStates(
              new Token(TOKEN_TYPE.REGCHAR, letter),
              dfaState,
            );
          } else {
            const dfaState = new NFAState(
              states[stateIndex].dfaState.id,
              states[stateIndex].dfaState.isAccept,
            );

            state.dfaState.addStates(
              new Token(TOKEN_TYPE.REGCHAR, letter),
              dfaState,
            );
          }
        }
      });
    }

    return {
      stateId,
      dfa,
    };
  }

  parseToDFA() {
    const beginTime = performance.now();
    let syntacticTree = this._syntacticTree();

    syntacticTree = calculatedFunctions(syntacticTree);
    this.leafs = _nextPosition(syntacticTree, this.leafs);
    const transitionsTable = this._transitionsTable(syntacticTree.firstPosition, this.leafs);
    const fsm = _toFSM(transitionsTable);

    const executionTime = performance.now() - beginTime;

    return {
      executionTime,
      fsm,
    };
  }
}

module.exports = DirectDFA;

},{"../constants":9,"../utils":56,"./DFANode":1,"./FSM":4,"./Lexer":5,"./NFAState":7,"lodash":10,"regexp-tree":54,"universal-perf-hooks":55}],3:[function(require,module,exports){
const DOTSCRIPTHEADER = 'digraph finite_state_machine {\n  rankdir = LR;\n';
const DOTSCRIPTEND = '}\n';

module.exports.toDotScript = function (fsm) {
  const states = [];
  let transitionDotScript = '  node [shape = circle];\n';
  for (const fromId in fsm.transitions) {
    for (const transition in fsm.transitions[fromId]) {
      let toId;
      let label;

      if (fsm.type === 'DirectDFA') {
        toId = fsm.transitions[fromId][transition];
        label = transition;
      } else {
        toId = transition;
        label = fsm.transitions[fromId][transition];
      }

      transitionDotScript += `  ${[fromId]}->${toId} [label="${label}"];\n`;

      if (states.findIndex((state) => state === fromId) === -1) {
        states.push(fromId);
      }
      if (states.findIndex((state) => state === toId) === -1) {
        states.push(toId);
      }
    }
  }
  let initialStatesDotScript = '';
  let initialStatesStartDotScript = '  node [shape = plaintext];\n';
  let acceptStatesDotScript = '';

  states.forEach((state) => {
    if (fsm.acceptStates.indexOf(state) !== -1) {
      acceptStatesDotScript += `  node [shape = doublecircle]; ${state};\n`;
    }
    if (fsm.initialState === state) {
      initialStatesStartDotScript += `  "" -> ${state} [label = "start"];\n`;
      // accept is higher priority than initial state.
      if (fsm.acceptStates.indexOf(state) === -1) { initialStatesDotScript += `  node [shape = circle]; ${state};\n`; }
    }
  });
  return DOTSCRIPTHEADER + initialStatesDotScript + acceptStatesDotScript
      + initialStatesStartDotScript + transitionDotScript + DOTSCRIPTEND;
};

},{}],4:[function(require,module,exports){
const { sortBy } = require('lodash');

const DotConverter = require('./DotConverter');
const { Lexer } = require('./Lexer');
const {
  TOKEN_TYPE,
} = require('../constants');

const _states = (transitions, state) => {
  if (transitions[state] !== undefined) {
    return Object.keys(transitions[state])
      .map((key) => ({
        id: key,
        label: transitions[state][key],
      }));
  }
  return [];
};

const _move = (fromStates, letter, transitions) => {
  let toStates = [];
  while (fromStates.length) {
    const fromState = fromStates.shift();
    const stack = _states(transitions, fromState);

    for (let i = 0; i < stack.length; i++) {
      const {
        id: nextId, label,
      } = stack[i];
      if (label === letter) {
        toStates.push(nextId);
      }
    }
  }

  toStates = sortBy(toStates);
  return toStates;
};

const _EPSILONClosure = (fromStates, transitions) => {
  let closure = [];
  const stack = [];
  for (let i = 0; i < fromStates.length; i++) {
    closure.push(fromStates[i]);
    stack.push(fromStates[i]);
  }

  while (stack.length) {
    const stateId = stack.shift();
    const states = _states(transitions, stateId);
    for (let i = 0; i < states.length; i++) {
      const {
        id: nextId, label,
      } = states[i];

      if (label === TOKEN_TYPE.EPSILON
        && closure.indexOf(nextId) === -1) {
        closure.push(nextId);
        stack.push(nextId);
      }
    }
  }
  closure = sortBy(closure);
  return closure;
};

class FSM {
  constructor() {
    this.initialState = '';
    this.acceptStates = [];
    this.numOfStates = 0;
    this.type = '';
    this.transitions = {};
  }

  toDotScript() {
    return DotConverter.toDotScript(this);
  }

  validateWord(word) {
    const lexer = new Lexer(word);

    const stateStack = [[this.initialState]];
    let validWord = false;

    let letter = lexer.nextToken().text;

    while (stateStack.length) {
      const actualStates = stateStack.shift();

      const epsilonStates = _EPSILONClosure(actualStates, this.transitions);
      const statesToMove = _move(
        epsilonStates,
        letter !== TOKEN_TYPE.END ? letter : TOKEN_TYPE.EPSILON,
        this.transitions,
      );

      if (letter !== TOKEN_TYPE.END) {
        letter = lexer.nextToken().text;
      }

      for (let i = 0; i < statesToMove.length; i++) {
        if (this.acceptStates.includes(statesToMove[i])
          && letter === TOKEN_TYPE.END) {
          validWord = true;
        }
      }

      if (statesToMove.length > 0) {
        stateStack.push(statesToMove);
      }
    }

    return validWord;
  }
}

module.exports = FSM;

},{"../constants":9,"./DotConverter":3,"./Lexer":5,"lodash":10}],5:[function(require,module,exports){
/* eslint-disable max-classes-per-file */
const { TOKEN_TYPE } = require('../constants');

function isRegChar(regChar) {
  return (regChar >= 'a' && regChar <= 'z')
         || (regChar >= 'A' && regChar <= 'Z')
         || (regChar >= '0' && regChar <= '9');
}

class Token {
  constructor(type, text) {
    this.type = type;
    this.text = text;
  }
}

const EPSILONTOKEN = new Token(TOKEN_TYPE.EPSILON, 'ε');

class Lexer {
  constructor(regString) {
    this.regString = regString;
    this.index = 0;
  }

  hasNext() {
    if (this.regString) {
      return this.index < this.regString.length;
    }

    return false;
  }

  nextToken() {
    while (this.hasNext()) {
      switch (this.regString[this.index]) {
        case 'ε':
          this._consume();
          return EPSILONTOKEN;
        case '(':
          this._consume();
          return new Token(TOKEN_TYPE.LBRACK, '(');
        case ')':
          this._consume();
          return new Token(TOKEN_TYPE.RBRACK, ')');
        case '*':
          this._consume();
          return new Token(TOKEN_TYPE.STAR, '*');
        case '|':
          this._consume();
          return new Token(TOKEN_TYPE.OR, '|');
        default:
          if (isRegChar(this.regString[this.index])) {
            return new Token(TOKEN_TYPE.REGCHAR, this.regString[this.index++]);
          }

          throw new Error(`Unknown type of ${this.regString[this.index]}`);
      }
    }
    return new Token(TOKEN_TYPE.END, 'EOF');
  }

  _consume() {
    return ++this.index;
  }
}

module.exports.Lexer = Lexer;
module.exports.EPSILONTOKEN = EPSILONTOKEN;
module.exports.TOKEN_TYPE = TOKEN_TYPE;
module.exports.Token = Token;

},{"../constants":9}],6:[function(require,module,exports){
/* eslint-disable global-require */
const { sortBy } = require('lodash');
const { performance } = require('universal-perf-hooks');

const FSM = require('./FSM');
const { TOKEN_TYPE } = require('./Lexer');

const _EPSILONClosure = (nfaStates, nfaGraph) => {
  let closure = [];
  const stack = [];
  for (let i = 0; i < nfaStates.length; ++i) {
    stack.push(nfaStates[i]);
    closure.push(nfaStates[i]);
  }
  while (stack.length) {
    const stateId = stack.shift();
    for (let i = 0; i < nfaGraph[stateId].length; ++i) {
      const nextId = nfaGraph[stateId][i][1];
      const label = nfaGraph[stateId][i][0];
      if (label === TOKEN_TYPE.EPSILON
        && closure.indexOf(nextId) === -1) {
        closure.push(nextId);
        stack.push(nextId);
      }
    }
  }
  closure = sortBy(closure);
  return closure;
};

const _move = (dfaState, letter, id2States, nfaGraph) => {
  const stateArray = id2States[dfaState.id];
  let result = [];
  for (let i = 0; i < stateArray.length; ++i) {
    const id = stateArray[i];
    for (let k = 0; k < nfaGraph[id].length; ++k) {
      const label = nfaGraph[id][k][0];
      if (label === letter) {
        result.push(nfaGraph[id][k][1]);
      }
    }
  }
  result = sortBy(result);
  return result;
};

const constructGraph = function (startState) {
  const nfaGraph = {};
  const queue = [];
  queue.push(startState);
  const vis = {};
  while (queue.length) {
    const state = queue.shift();
    nfaGraph[state.id] = [];
    for (let i = 0; i < (state.nextStates).length; ++i) {
      const nextId = state.nextStates[i][1].id;
      const label = state.nextStates[i][0].text;
      // const nextState = state.nextStates[i][1];
      nfaGraph[state.id].push([label, nextId]);
      if (nextId in vis) {
        continue;
      }
      vis[nextId] = 1;
      queue.push(state.nextStates[i][1]);
    }
  }

  return nfaGraph;
};

class NFA {
  constructor(startState, endState) {
    this.startState = startState;
    this.endState = endState;
  }

  toDFA() {
    const beginTime = performance.now();

    const nfaGraph = constructGraph(this.startState);
    const alphabetTable = {};
    for (const id in nfaGraph) {
      for (let j = 0; j < nfaGraph[id].length; ++j) {
        const label = nfaGraph[id][j][0];
        if (!alphabetTable.hasOwnProperty(label)
          && label !== TOKEN_TYPE.EPSILON) {
          alphabetTable[label] = 1;
        }
      }
    }

    const dStates = [];
    const states2Id = {}; // [1, 2, 3] => id
    const id2States = {}; // id => [1, 2, 3]
    let id = 0;
    const closure = _EPSILONClosure([this.startState.id], nfaGraph);
    states2Id[JSON.stringify(closure)] = id;
    id2States[id] = closure;
    dStates.push({ id: id++, nextStates: {}, vis: false });

    dStates[dStates.length - 1].accept = closure.indexOf(this.endState.id) !== -1;
    dStates[dStates.length - 1].initial = closure.indexOf(this.startState.id) !== -1;
    let unvisCnt = 1;
    while (unvisCnt) {
      const [unvisState] = dStates.filter((state) => !state.vis);
      unvisState.vis = true;
      --unvisCnt;
      for (const letter in alphabetTable) {
        if (letter === TOKEN_TYPE.EPSILON) { continue; }

        const nextStates = _EPSILONClosure(
          _move(unvisState, letter, id2States, nfaGraph), nfaGraph,
        );

        if (!nextStates.length) { continue; }
        const nextStatesString = JSON.stringify(nextStates);
        if (!states2Id.hasOwnProperty(nextStatesString)) {
          states2Id[nextStatesString] = id;
          id2States[id] = nextStates;
          dStates.push({
            id: id++,
            nextStates: {},
            vis: false,
            accept: nextStates.indexOf(this.endState.id) !== -1,
            initial: nextStates.indexOf(this.startState.id) !== -1,
          });
          ++unvisCnt;
        }

        unvisState.nextStates[letter] = nextStates;
      }
    }

    const dfa = new FSM();
    dfa.type = 'DFA';
    dfa.numOfStates = id;
    const numberToLetter = (number) => 'ABCDEFGHIJKLMNÑOPQRSTUVWXYZ'[number];

    for (let i = 0; i < dStates.length; ++i) {
      if (dStates[i].initial) { dfa.initialState = numberToLetter(dStates[i].id); }
      if (dStates[i].accept) { dfa.acceptStates.push(numberToLetter(dStates[i].id)); }

      for (const letter in alphabetTable) {
        if (!dStates[i].nextStates[letter]) { continue; }
        const arrayId = [];
        for (let j = 0; j < dStates[i].nextStates[letter].length; ++j) {
          arrayId.push(dStates[i].nextStates[letter][j]);
        }

        if (arrayId.length) {
          if (!dfa.transitions[numberToLetter(dStates[i].id)]) {
            dfa.transitions[numberToLetter(dStates[i].id)] = {};
          }

          dfa.transitions[
            numberToLetter(dStates[i].id)
          ][
            numberToLetter(states2Id[JSON.stringify(arrayId)])
          ] = letter;
        }
      }
    }

    const executionTime = performance.now() - beginTime;
    return {
      executionTime,
      dfa,
    };
  }
}

module.exports = NFA;

},{"./FSM":4,"./Lexer":5,"lodash":10,"universal-perf-hooks":55}],7:[function(require,module,exports){
class NFAState {
  constructor(id, isAccept, isInitial = false) {
    this.id = id;
    this.isAccept = isAccept;
    this.isInitial = isInitial;
    this.nextStates = [];
  }

  addStates(token, state) {
    this.nextStates.push([token, state]);
  }
}

module.exports = NFAState;

},{}],8:[function(require,module,exports){
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

},{"../utils":56,"./FSM":4,"./Lexer":5,"./NFA":6,"./NFAState":7,"universal-perf-hooks":55}],9:[function(require,module,exports){
module.exports.TOKEN_TYPE = {
  LBRACK: '(',
  RBRACK: ')',
  STAR: '*',
  OR: '|',
  END: 'EOF',
  EPSILON: 'ε',
  BLANK: ' ',
  REGCHAR: 'a-z0-9',
  INCREASED: '#',
};

module.exports.REG_TREE_TYPE = {
  Alternative: 'Alternative',
  Char: 'Char',
  Group: 'Group',
  Or: 'Disjunction',
  Kleen: 'Repetition',
};

module.exports.DFA_NODE_TYPE = {
  increased: '#',
  leaf: 'leaf',
  node: 'node',
  root: 'root',
};

},{}],10:[function(require,module,exports){
(function (global){
/**
 * @license
 * Lodash <https://lodash.com/>
 * Copyright OpenJS Foundation and other contributors <https://openjsf.org/>
 * Released under MIT license <https://lodash.com/license>
 * Based on Underscore.js 1.8.3 <http://underscorejs.org/LICENSE>
 * Copyright Jeremy Ashkenas, DocumentCloud and Investigative Reporters & Editors
 */
;(function() {

  /** Used as a safe reference for `undefined` in pre-ES5 environments. */
  var undefined;

  /** Used as the semantic version number. */
  var VERSION = '4.17.21';

  /** Used as the size to enable large array optimizations. */
  var LARGE_ARRAY_SIZE = 200;

  /** Error message constants. */
  var CORE_ERROR_TEXT = 'Unsupported core-js use. Try https://npms.io/search?q=ponyfill.',
      FUNC_ERROR_TEXT = 'Expected a function',
      INVALID_TEMPL_VAR_ERROR_TEXT = 'Invalid `variable` option passed into `_.template`';

  /** Used to stand-in for `undefined` hash values. */
  var HASH_UNDEFINED = '__lodash_hash_undefined__';

  /** Used as the maximum memoize cache size. */
  var MAX_MEMOIZE_SIZE = 500;

  /** Used as the internal argument placeholder. */
  var PLACEHOLDER = '__lodash_placeholder__';

  /** Used to compose bitmasks for cloning. */
  var CLONE_DEEP_FLAG = 1,
      CLONE_FLAT_FLAG = 2,
      CLONE_SYMBOLS_FLAG = 4;

  /** Used to compose bitmasks for value comparisons. */
  var COMPARE_PARTIAL_FLAG = 1,
      COMPARE_UNORDERED_FLAG = 2;

  /** Used to compose bitmasks for function metadata. */
  var WRAP_BIND_FLAG = 1,
      WRAP_BIND_KEY_FLAG = 2,
      WRAP_CURRY_BOUND_FLAG = 4,
      WRAP_CURRY_FLAG = 8,
      WRAP_CURRY_RIGHT_FLAG = 16,
      WRAP_PARTIAL_FLAG = 32,
      WRAP_PARTIAL_RIGHT_FLAG = 64,
      WRAP_ARY_FLAG = 128,
      WRAP_REARG_FLAG = 256,
      WRAP_FLIP_FLAG = 512;

  /** Used as default options for `_.truncate`. */
  var DEFAULT_TRUNC_LENGTH = 30,
      DEFAULT_TRUNC_OMISSION = '...';

  /** Used to detect hot functions by number of calls within a span of milliseconds. */
  var HOT_COUNT = 800,
      HOT_SPAN = 16;

  /** Used to indicate the type of lazy iteratees. */
  var LAZY_FILTER_FLAG = 1,
      LAZY_MAP_FLAG = 2,
      LAZY_WHILE_FLAG = 3;

  /** Used as references for various `Number` constants. */
  var INFINITY = 1 / 0,
      MAX_SAFE_INTEGER = 9007199254740991,
      MAX_INTEGER = 1.7976931348623157e+308,
      NAN = 0 / 0;

  /** Used as references for the maximum length and index of an array. */
  var MAX_ARRAY_LENGTH = 4294967295,
      MAX_ARRAY_INDEX = MAX_ARRAY_LENGTH - 1,
      HALF_MAX_ARRAY_LENGTH = MAX_ARRAY_LENGTH >>> 1;

  /** Used to associate wrap methods with their bit flags. */
  var wrapFlags = [
    ['ary', WRAP_ARY_FLAG],
    ['bind', WRAP_BIND_FLAG],
    ['bindKey', WRAP_BIND_KEY_FLAG],
    ['curry', WRAP_CURRY_FLAG],
    ['curryRight', WRAP_CURRY_RIGHT_FLAG],
    ['flip', WRAP_FLIP_FLAG],
    ['partial', WRAP_PARTIAL_FLAG],
    ['partialRight', WRAP_PARTIAL_RIGHT_FLAG],
    ['rearg', WRAP_REARG_FLAG]
  ];

  /** `Object#toString` result references. */
  var argsTag = '[object Arguments]',
      arrayTag = '[object Array]',
      asyncTag = '[object AsyncFunction]',
      boolTag = '[object Boolean]',
      dateTag = '[object Date]',
      domExcTag = '[object DOMException]',
      errorTag = '[object Error]',
      funcTag = '[object Function]',
      genTag = '[object GeneratorFunction]',
      mapTag = '[object Map]',
      numberTag = '[object Number]',
      nullTag = '[object Null]',
      objectTag = '[object Object]',
      promiseTag = '[object Promise]',
      proxyTag = '[object Proxy]',
      regexpTag = '[object RegExp]',
      setTag = '[object Set]',
      stringTag = '[object String]',
      symbolTag = '[object Symbol]',
      undefinedTag = '[object Undefined]',
      weakMapTag = '[object WeakMap]',
      weakSetTag = '[object WeakSet]';

  var arrayBufferTag = '[object ArrayBuffer]',
      dataViewTag = '[object DataView]',
      float32Tag = '[object Float32Array]',
      float64Tag = '[object Float64Array]',
      int8Tag = '[object Int8Array]',
      int16Tag = '[object Int16Array]',
      int32Tag = '[object Int32Array]',
      uint8Tag = '[object Uint8Array]',
      uint8ClampedTag = '[object Uint8ClampedArray]',
      uint16Tag = '[object Uint16Array]',
      uint32Tag = '[object Uint32Array]';

  /** Used to match empty string literals in compiled template source. */
  var reEmptyStringLeading = /\b__p \+= '';/g,
      reEmptyStringMiddle = /\b(__p \+=) '' \+/g,
      reEmptyStringTrailing = /(__e\(.*?\)|\b__t\)) \+\n'';/g;

  /** Used to match HTML entities and HTML characters. */
  var reEscapedHtml = /&(?:amp|lt|gt|quot|#39);/g,
      reUnescapedHtml = /[&<>"']/g,
      reHasEscapedHtml = RegExp(reEscapedHtml.source),
      reHasUnescapedHtml = RegExp(reUnescapedHtml.source);

  /** Used to match template delimiters. */
  var reEscape = /<%-([\s\S]+?)%>/g,
      reEvaluate = /<%([\s\S]+?)%>/g,
      reInterpolate = /<%=([\s\S]+?)%>/g;

  /** Used to match property names within property paths. */
  var reIsDeepProp = /\.|\[(?:[^[\]]*|(["'])(?:(?!\1)[^\\]|\\.)*?\1)\]/,
      reIsPlainProp = /^\w*$/,
      rePropName = /[^.[\]]+|\[(?:(-?\d+(?:\.\d+)?)|(["'])((?:(?!\2)[^\\]|\\.)*?)\2)\]|(?=(?:\.|\[\])(?:\.|\[\]|$))/g;

  /**
   * Used to match `RegExp`
   * [syntax characters](http://ecma-international.org/ecma-262/7.0/#sec-patterns).
   */
  var reRegExpChar = /[\\^$.*+?()[\]{}|]/g,
      reHasRegExpChar = RegExp(reRegExpChar.source);

  /** Used to match leading whitespace. */
  var reTrimStart = /^\s+/;

  /** Used to match a single whitespace character. */
  var reWhitespace = /\s/;

  /** Used to match wrap detail comments. */
  var reWrapComment = /\{(?:\n\/\* \[wrapped with .+\] \*\/)?\n?/,
      reWrapDetails = /\{\n\/\* \[wrapped with (.+)\] \*/,
      reSplitDetails = /,? & /;

  /** Used to match words composed of alphanumeric characters. */
  var reAsciiWord = /[^\x00-\x2f\x3a-\x40\x5b-\x60\x7b-\x7f]+/g;

  /**
   * Used to validate the `validate` option in `_.template` variable.
   *
   * Forbids characters which could potentially change the meaning of the function argument definition:
   * - "()," (modification of function parameters)
   * - "=" (default value)
   * - "[]{}" (destructuring of function parameters)
   * - "/" (beginning of a comment)
   * - whitespace
   */
  var reForbiddenIdentifierChars = /[()=,{}\[\]\/\s]/;

  /** Used to match backslashes in property paths. */
  var reEscapeChar = /\\(\\)?/g;

  /**
   * Used to match
   * [ES template delimiters](http://ecma-international.org/ecma-262/7.0/#sec-template-literal-lexical-components).
   */
  var reEsTemplate = /\$\{([^\\}]*(?:\\.[^\\}]*)*)\}/g;

  /** Used to match `RegExp` flags from their coerced string values. */
  var reFlags = /\w*$/;

  /** Used to detect bad signed hexadecimal string values. */
  var reIsBadHex = /^[-+]0x[0-9a-f]+$/i;

  /** Used to detect binary string values. */
  var reIsBinary = /^0b[01]+$/i;

  /** Used to detect host constructors (Safari). */
  var reIsHostCtor = /^\[object .+?Constructor\]$/;

  /** Used to detect octal string values. */
  var reIsOctal = /^0o[0-7]+$/i;

  /** Used to detect unsigned integer values. */
  var reIsUint = /^(?:0|[1-9]\d*)$/;

  /** Used to match Latin Unicode letters (excluding mathematical operators). */
  var reLatin = /[\xc0-\xd6\xd8-\xf6\xf8-\xff\u0100-\u017f]/g;

  /** Used to ensure capturing order of template delimiters. */
  var reNoMatch = /($^)/;

  /** Used to match unescaped characters in compiled string literals. */
  var reUnescapedString = /['\n\r\u2028\u2029\\]/g;

  /** Used to compose unicode character classes. */
  var rsAstralRange = '\\ud800-\\udfff',
      rsComboMarksRange = '\\u0300-\\u036f',
      reComboHalfMarksRange = '\\ufe20-\\ufe2f',
      rsComboSymbolsRange = '\\u20d0-\\u20ff',
      rsComboRange = rsComboMarksRange + reComboHalfMarksRange + rsComboSymbolsRange,
      rsDingbatRange = '\\u2700-\\u27bf',
      rsLowerRange = 'a-z\\xdf-\\xf6\\xf8-\\xff',
      rsMathOpRange = '\\xac\\xb1\\xd7\\xf7',
      rsNonCharRange = '\\x00-\\x2f\\x3a-\\x40\\x5b-\\x60\\x7b-\\xbf',
      rsPunctuationRange = '\\u2000-\\u206f',
      rsSpaceRange = ' \\t\\x0b\\f\\xa0\\ufeff\\n\\r\\u2028\\u2029\\u1680\\u180e\\u2000\\u2001\\u2002\\u2003\\u2004\\u2005\\u2006\\u2007\\u2008\\u2009\\u200a\\u202f\\u205f\\u3000',
      rsUpperRange = 'A-Z\\xc0-\\xd6\\xd8-\\xde',
      rsVarRange = '\\ufe0e\\ufe0f',
      rsBreakRange = rsMathOpRange + rsNonCharRange + rsPunctuationRange + rsSpaceRange;

  /** Used to compose unicode capture groups. */
  var rsApos = "['\u2019]",
      rsAstral = '[' + rsAstralRange + ']',
      rsBreak = '[' + rsBreakRange + ']',
      rsCombo = '[' + rsComboRange + ']',
      rsDigits = '\\d+',
      rsDingbat = '[' + rsDingbatRange + ']',
      rsLower = '[' + rsLowerRange + ']',
      rsMisc = '[^' + rsAstralRange + rsBreakRange + rsDigits + rsDingbatRange + rsLowerRange + rsUpperRange + ']',
      rsFitz = '\\ud83c[\\udffb-\\udfff]',
      rsModifier = '(?:' + rsCombo + '|' + rsFitz + ')',
      rsNonAstral = '[^' + rsAstralRange + ']',
      rsRegional = '(?:\\ud83c[\\udde6-\\uddff]){2}',
      rsSurrPair = '[\\ud800-\\udbff][\\udc00-\\udfff]',
      rsUpper = '[' + rsUpperRange + ']',
      rsZWJ = '\\u200d';

  /** Used to compose unicode regexes. */
  var rsMiscLower = '(?:' + rsLower + '|' + rsMisc + ')',
      rsMiscUpper = '(?:' + rsUpper + '|' + rsMisc + ')',
      rsOptContrLower = '(?:' + rsApos + '(?:d|ll|m|re|s|t|ve))?',
      rsOptContrUpper = '(?:' + rsApos + '(?:D|LL|M|RE|S|T|VE))?',
      reOptMod = rsModifier + '?',
      rsOptVar = '[' + rsVarRange + ']?',
      rsOptJoin = '(?:' + rsZWJ + '(?:' + [rsNonAstral, rsRegional, rsSurrPair].join('|') + ')' + rsOptVar + reOptMod + ')*',
      rsOrdLower = '\\d*(?:1st|2nd|3rd|(?![123])\\dth)(?=\\b|[A-Z_])',
      rsOrdUpper = '\\d*(?:1ST|2ND|3RD|(?![123])\\dTH)(?=\\b|[a-z_])',
      rsSeq = rsOptVar + reOptMod + rsOptJoin,
      rsEmoji = '(?:' + [rsDingbat, rsRegional, rsSurrPair].join('|') + ')' + rsSeq,
      rsSymbol = '(?:' + [rsNonAstral + rsCombo + '?', rsCombo, rsRegional, rsSurrPair, rsAstral].join('|') + ')';

  /** Used to match apostrophes. */
  var reApos = RegExp(rsApos, 'g');

  /**
   * Used to match [combining diacritical marks](https://en.wikipedia.org/wiki/Combining_Diacritical_Marks) and
   * [combining diacritical marks for symbols](https://en.wikipedia.org/wiki/Combining_Diacritical_Marks_for_Symbols).
   */
  var reComboMark = RegExp(rsCombo, 'g');

  /** Used to match [string symbols](https://mathiasbynens.be/notes/javascript-unicode). */
  var reUnicode = RegExp(rsFitz + '(?=' + rsFitz + ')|' + rsSymbol + rsSeq, 'g');

  /** Used to match complex or compound words. */
  var reUnicodeWord = RegExp([
    rsUpper + '?' + rsLower + '+' + rsOptContrLower + '(?=' + [rsBreak, rsUpper, '$'].join('|') + ')',
    rsMiscUpper + '+' + rsOptContrUpper + '(?=' + [rsBreak, rsUpper + rsMiscLower, '$'].join('|') + ')',
    rsUpper + '?' + rsMiscLower + '+' + rsOptContrLower,
    rsUpper + '+' + rsOptContrUpper,
    rsOrdUpper,
    rsOrdLower,
    rsDigits,
    rsEmoji
  ].join('|'), 'g');

  /** Used to detect strings with [zero-width joiners or code points from the astral planes](http://eev.ee/blog/2015/09/12/dark-corners-of-unicode/). */
  var reHasUnicode = RegExp('[' + rsZWJ + rsAstralRange  + rsComboRange + rsVarRange + ']');

  /** Used to detect strings that need a more robust regexp to match words. */
  var reHasUnicodeWord = /[a-z][A-Z]|[A-Z]{2}[a-z]|[0-9][a-zA-Z]|[a-zA-Z][0-9]|[^a-zA-Z0-9 ]/;

  /** Used to assign default `context` object properties. */
  var contextProps = [
    'Array', 'Buffer', 'DataView', 'Date', 'Error', 'Float32Array', 'Float64Array',
    'Function', 'Int8Array', 'Int16Array', 'Int32Array', 'Map', 'Math', 'Object',
    'Promise', 'RegExp', 'Set', 'String', 'Symbol', 'TypeError', 'Uint8Array',
    'Uint8ClampedArray', 'Uint16Array', 'Uint32Array', 'WeakMap',
    '_', 'clearTimeout', 'isFinite', 'parseInt', 'setTimeout'
  ];

  /** Used to make template sourceURLs easier to identify. */
  var templateCounter = -1;

  /** Used to identify `toStringTag` values of typed arrays. */
  var typedArrayTags = {};
  typedArrayTags[float32Tag] = typedArrayTags[float64Tag] =
  typedArrayTags[int8Tag] = typedArrayTags[int16Tag] =
  typedArrayTags[int32Tag] = typedArrayTags[uint8Tag] =
  typedArrayTags[uint8ClampedTag] = typedArrayTags[uint16Tag] =
  typedArrayTags[uint32Tag] = true;
  typedArrayTags[argsTag] = typedArrayTags[arrayTag] =
  typedArrayTags[arrayBufferTag] = typedArrayTags[boolTag] =
  typedArrayTags[dataViewTag] = typedArrayTags[dateTag] =
  typedArrayTags[errorTag] = typedArrayTags[funcTag] =
  typedArrayTags[mapTag] = typedArrayTags[numberTag] =
  typedArrayTags[objectTag] = typedArrayTags[regexpTag] =
  typedArrayTags[setTag] = typedArrayTags[stringTag] =
  typedArrayTags[weakMapTag] = false;

  /** Used to identify `toStringTag` values supported by `_.clone`. */
  var cloneableTags = {};
  cloneableTags[argsTag] = cloneableTags[arrayTag] =
  cloneableTags[arrayBufferTag] = cloneableTags[dataViewTag] =
  cloneableTags[boolTag] = cloneableTags[dateTag] =
  cloneableTags[float32Tag] = cloneableTags[float64Tag] =
  cloneableTags[int8Tag] = cloneableTags[int16Tag] =
  cloneableTags[int32Tag] = cloneableTags[mapTag] =
  cloneableTags[numberTag] = cloneableTags[objectTag] =
  cloneableTags[regexpTag] = cloneableTags[setTag] =
  cloneableTags[stringTag] = cloneableTags[symbolTag] =
  cloneableTags[uint8Tag] = cloneableTags[uint8ClampedTag] =
  cloneableTags[uint16Tag] = cloneableTags[uint32Tag] = true;
  cloneableTags[errorTag] = cloneableTags[funcTag] =
  cloneableTags[weakMapTag] = false;

  /** Used to map Latin Unicode letters to basic Latin letters. */
  var deburredLetters = {
    // Latin-1 Supplement block.
    '\xc0': 'A',  '\xc1': 'A', '\xc2': 'A', '\xc3': 'A', '\xc4': 'A', '\xc5': 'A',
    '\xe0': 'a',  '\xe1': 'a', '\xe2': 'a', '\xe3': 'a', '\xe4': 'a', '\xe5': 'a',
    '\xc7': 'C',  '\xe7': 'c',
    '\xd0': 'D',  '\xf0': 'd',
    '\xc8': 'E',  '\xc9': 'E', '\xca': 'E', '\xcb': 'E',
    '\xe8': 'e',  '\xe9': 'e', '\xea': 'e', '\xeb': 'e',
    '\xcc': 'I',  '\xcd': 'I', '\xce': 'I', '\xcf': 'I',
    '\xec': 'i',  '\xed': 'i', '\xee': 'i', '\xef': 'i',
    '\xd1': 'N',  '\xf1': 'n',
    '\xd2': 'O',  '\xd3': 'O', '\xd4': 'O', '\xd5': 'O', '\xd6': 'O', '\xd8': 'O',
    '\xf2': 'o',  '\xf3': 'o', '\xf4': 'o', '\xf5': 'o', '\xf6': 'o', '\xf8': 'o',
    '\xd9': 'U',  '\xda': 'U', '\xdb': 'U', '\xdc': 'U',
    '\xf9': 'u',  '\xfa': 'u', '\xfb': 'u', '\xfc': 'u',
    '\xdd': 'Y',  '\xfd': 'y', '\xff': 'y',
    '\xc6': 'Ae', '\xe6': 'ae',
    '\xde': 'Th', '\xfe': 'th',
    '\xdf': 'ss',
    // Latin Extended-A block.
    '\u0100': 'A',  '\u0102': 'A', '\u0104': 'A',
    '\u0101': 'a',  '\u0103': 'a', '\u0105': 'a',
    '\u0106': 'C',  '\u0108': 'C', '\u010a': 'C', '\u010c': 'C',
    '\u0107': 'c',  '\u0109': 'c', '\u010b': 'c', '\u010d': 'c',
    '\u010e': 'D',  '\u0110': 'D', '\u010f': 'd', '\u0111': 'd',
    '\u0112': 'E',  '\u0114': 'E', '\u0116': 'E', '\u0118': 'E', '\u011a': 'E',
    '\u0113': 'e',  '\u0115': 'e', '\u0117': 'e', '\u0119': 'e', '\u011b': 'e',
    '\u011c': 'G',  '\u011e': 'G', '\u0120': 'G', '\u0122': 'G',
    '\u011d': 'g',  '\u011f': 'g', '\u0121': 'g', '\u0123': 'g',
    '\u0124': 'H',  '\u0126': 'H', '\u0125': 'h', '\u0127': 'h',
    '\u0128': 'I',  '\u012a': 'I', '\u012c': 'I', '\u012e': 'I', '\u0130': 'I',
    '\u0129': 'i',  '\u012b': 'i', '\u012d': 'i', '\u012f': 'i', '\u0131': 'i',
    '\u0134': 'J',  '\u0135': 'j',
    '\u0136': 'K',  '\u0137': 'k', '\u0138': 'k',
    '\u0139': 'L',  '\u013b': 'L', '\u013d': 'L', '\u013f': 'L', '\u0141': 'L',
    '\u013a': 'l',  '\u013c': 'l', '\u013e': 'l', '\u0140': 'l', '\u0142': 'l',
    '\u0143': 'N',  '\u0145': 'N', '\u0147': 'N', '\u014a': 'N',
    '\u0144': 'n',  '\u0146': 'n', '\u0148': 'n', '\u014b': 'n',
    '\u014c': 'O',  '\u014e': 'O', '\u0150': 'O',
    '\u014d': 'o',  '\u014f': 'o', '\u0151': 'o',
    '\u0154': 'R',  '\u0156': 'R', '\u0158': 'R',
    '\u0155': 'r',  '\u0157': 'r', '\u0159': 'r',
    '\u015a': 'S',  '\u015c': 'S', '\u015e': 'S', '\u0160': 'S',
    '\u015b': 's',  '\u015d': 's', '\u015f': 's', '\u0161': 's',
    '\u0162': 'T',  '\u0164': 'T', '\u0166': 'T',
    '\u0163': 't',  '\u0165': 't', '\u0167': 't',
    '\u0168': 'U',  '\u016a': 'U', '\u016c': 'U', '\u016e': 'U', '\u0170': 'U', '\u0172': 'U',
    '\u0169': 'u',  '\u016b': 'u', '\u016d': 'u', '\u016f': 'u', '\u0171': 'u', '\u0173': 'u',
    '\u0174': 'W',  '\u0175': 'w',
    '\u0176': 'Y',  '\u0177': 'y', '\u0178': 'Y',
    '\u0179': 'Z',  '\u017b': 'Z', '\u017d': 'Z',
    '\u017a': 'z',  '\u017c': 'z', '\u017e': 'z',
    '\u0132': 'IJ', '\u0133': 'ij',
    '\u0152': 'Oe', '\u0153': 'oe',
    '\u0149': "'n", '\u017f': 's'
  };

  /** Used to map characters to HTML entities. */
  var htmlEscapes = {
    '&': '&amp;',
    '<': '&lt;',
    '>': '&gt;',
    '"': '&quot;',
    "'": '&#39;'
  };

  /** Used to map HTML entities to characters. */
  var htmlUnescapes = {
    '&amp;': '&',
    '&lt;': '<',
    '&gt;': '>',
    '&quot;': '"',
    '&#39;': "'"
  };

  /** Used to escape characters for inclusion in compiled string literals. */
  var stringEscapes = {
    '\\': '\\',
    "'": "'",
    '\n': 'n',
    '\r': 'r',
    '\u2028': 'u2028',
    '\u2029': 'u2029'
  };

  /** Built-in method references without a dependency on `root`. */
  var freeParseFloat = parseFloat,
      freeParseInt = parseInt;

  /** Detect free variable `global` from Node.js. */
  var freeGlobal = typeof global == 'object' && global && global.Object === Object && global;

  /** Detect free variable `self`. */
  var freeSelf = typeof self == 'object' && self && self.Object === Object && self;

  /** Used as a reference to the global object. */
  var root = freeGlobal || freeSelf || Function('return this')();

  /** Detect free variable `exports`. */
  var freeExports = typeof exports == 'object' && exports && !exports.nodeType && exports;

  /** Detect free variable `module`. */
  var freeModule = freeExports && typeof module == 'object' && module && !module.nodeType && module;

  /** Detect the popular CommonJS extension `module.exports`. */
  var moduleExports = freeModule && freeModule.exports === freeExports;

  /** Detect free variable `process` from Node.js. */
  var freeProcess = moduleExports && freeGlobal.process;

  /** Used to access faster Node.js helpers. */
  var nodeUtil = (function() {
    try {
      // Use `util.types` for Node.js 10+.
      var types = freeModule && freeModule.require && freeModule.require('util').types;

      if (types) {
        return types;
      }

      // Legacy `process.binding('util')` for Node.js < 10.
      return freeProcess && freeProcess.binding && freeProcess.binding('util');
    } catch (e) {}
  }());

  /* Node.js helper references. */
  var nodeIsArrayBuffer = nodeUtil && nodeUtil.isArrayBuffer,
      nodeIsDate = nodeUtil && nodeUtil.isDate,
      nodeIsMap = nodeUtil && nodeUtil.isMap,
      nodeIsRegExp = nodeUtil && nodeUtil.isRegExp,
      nodeIsSet = nodeUtil && nodeUtil.isSet,
      nodeIsTypedArray = nodeUtil && nodeUtil.isTypedArray;

  /*--------------------------------------------------------------------------*/

  /**
   * A faster alternative to `Function#apply`, this function invokes `func`
   * with the `this` binding of `thisArg` and the arguments of `args`.
   *
   * @private
   * @param {Function} func The function to invoke.
   * @param {*} thisArg The `this` binding of `func`.
   * @param {Array} args The arguments to invoke `func` with.
   * @returns {*} Returns the result of `func`.
   */
  function apply(func, thisArg, args) {
    switch (args.length) {
      case 0: return func.call(thisArg);
      case 1: return func.call(thisArg, args[0]);
      case 2: return func.call(thisArg, args[0], args[1]);
      case 3: return func.call(thisArg, args[0], args[1], args[2]);
    }
    return func.apply(thisArg, args);
  }

  /**
   * A specialized version of `baseAggregator` for arrays.
   *
   * @private
   * @param {Array} [array] The array to iterate over.
   * @param {Function} setter The function to set `accumulator` values.
   * @param {Function} iteratee The iteratee to transform keys.
   * @param {Object} accumulator The initial aggregated object.
   * @returns {Function} Returns `accumulator`.
   */
  function arrayAggregator(array, setter, iteratee, accumulator) {
    var index = -1,
        length = array == null ? 0 : array.length;

    while (++index < length) {
      var value = array[index];
      setter(accumulator, value, iteratee(value), array);
    }
    return accumulator;
  }

  /**
   * A specialized version of `_.forEach` for arrays without support for
   * iteratee shorthands.
   *
   * @private
   * @param {Array} [array] The array to iterate over.
   * @param {Function} iteratee The function invoked per iteration.
   * @returns {Array} Returns `array`.
   */
  function arrayEach(array, iteratee) {
    var index = -1,
        length = array == null ? 0 : array.length;

    while (++index < length) {
      if (iteratee(array[index], index, array) === false) {
        break;
      }
    }
    return array;
  }

  /**
   * A specialized version of `_.forEachRight` for arrays without support for
   * iteratee shorthands.
   *
   * @private
   * @param {Array} [array] The array to iterate over.
   * @param {Function} iteratee The function invoked per iteration.
   * @returns {Array} Returns `array`.
   */
  function arrayEachRight(array, iteratee) {
    var length = array == null ? 0 : array.length;

    while (length--) {
      if (iteratee(array[length], length, array) === false) {
        break;
      }
    }
    return array;
  }

  /**
   * A specialized version of `_.every` for arrays without support for
   * iteratee shorthands.
   *
   * @private
   * @param {Array} [array] The array to iterate over.
   * @param {Function} predicate The function invoked per iteration.
   * @returns {boolean} Returns `true` if all elements pass the predicate check,
   *  else `false`.
   */
  function arrayEvery(array, predicate) {
    var index = -1,
        length = array == null ? 0 : array.length;

    while (++index < length) {
      if (!predicate(array[index], index, array)) {
        return false;
      }
    }
    return true;
  }

  /**
   * A specialized version of `_.filter` for arrays without support for
   * iteratee shorthands.
   *
   * @private
   * @param {Array} [array] The array to iterate over.
   * @param {Function} predicate The function invoked per iteration.
   * @returns {Array} Returns the new filtered array.
   */
  function arrayFilter(array, predicate) {
    var index = -1,
        length = array == null ? 0 : array.length,
        resIndex = 0,
        result = [];

    while (++index < length) {
      var value = array[index];
      if (predicate(value, index, array)) {
        result[resIndex++] = value;
      }
    }
    return result;
  }

  /**
   * A specialized version of `_.includes` for arrays without support for
   * specifying an index to search from.
   *
   * @private
   * @param {Array} [array] The array to inspect.
   * @param {*} target The value to search for.
   * @returns {boolean} Returns `true` if `target` is found, else `false`.
   */
  function arrayIncludes(array, value) {
    var length = array == null ? 0 : array.length;
    return !!length && baseIndexOf(array, value, 0) > -1;
  }

  /**
   * This function is like `arrayIncludes` except that it accepts a comparator.
   *
   * @private
   * @param {Array} [array] The array to inspect.
   * @param {*} target The value to search for.
   * @param {Function} comparator The comparator invoked per element.
   * @returns {boolean} Returns `true` if `target` is found, else `false`.
   */
  function arrayIncludesWith(array, value, comparator) {
    var index = -1,
        length = array == null ? 0 : array.length;

    while (++index < length) {
      if (comparator(value, array[index])) {
        return true;
      }
    }
    return false;
  }

  /**
   * A specialized version of `_.map` for arrays without support for iteratee
   * shorthands.
   *
   * @private
   * @param {Array} [array] The array to iterate over.
   * @param {Function} iteratee The function invoked per iteration.
   * @returns {Array} Returns the new mapped array.
   */
  function arrayMap(array, iteratee) {
    var index = -1,
        length = array == null ? 0 : array.length,
        result = Array(length);

    while (++index < length) {
      result[index] = iteratee(array[index], index, array);
    }
    return result;
  }

  /**
   * Appends the elements of `values` to `array`.
   *
   * @private
   * @param {Array} array The array to modify.
   * @param {Array} values The values to append.
   * @returns {Array} Returns `array`.
   */
  function arrayPush(array, values) {
    var index = -1,
        length = values.length,
        offset = array.length;

    while (++index < length) {
      array[offset + index] = values[index];
    }
    return array;
  }

  /**
   * A specialized version of `_.reduce` for arrays without support for
   * iteratee shorthands.
   *
   * @private
   * @param {Array} [array] The array to iterate over.
   * @param {Function} iteratee The function invoked per iteration.
   * @param {*} [accumulator] The initial value.
   * @param {boolean} [initAccum] Specify using the first element of `array` as
   *  the initial value.
   * @returns {*} Returns the accumulated value.
   */
  function arrayReduce(array, iteratee, accumulator, initAccum) {
    var index = -1,
        length = array == null ? 0 : array.length;

    if (initAccum && length) {
      accumulator = array[++index];
    }
    while (++index < length) {
      accumulator = iteratee(accumulator, array[index], index, array);
    }
    return accumulator;
  }

  /**
   * A specialized version of `_.reduceRight` for arrays without support for
   * iteratee shorthands.
   *
   * @private
   * @param {Array} [array] The array to iterate over.
   * @param {Function} iteratee The function invoked per iteration.
   * @param {*} [accumulator] The initial value.
   * @param {boolean} [initAccum] Specify using the last element of `array` as
   *  the initial value.
   * @returns {*} Returns the accumulated value.
   */
  function arrayReduceRight(array, iteratee, accumulator, initAccum) {
    var length = array == null ? 0 : array.length;
    if (initAccum && length) {
      accumulator = array[--length];
    }
    while (length--) {
      accumulator = iteratee(accumulator, array[length], length, array);
    }
    return accumulator;
  }

  /**
   * A specialized version of `_.some` for arrays without support for iteratee
   * shorthands.
   *
   * @private
   * @param {Array} [array] The array to iterate over.
   * @param {Function} predicate The function invoked per iteration.
   * @returns {boolean} Returns `true` if any element passes the predicate check,
   *  else `false`.
   */
  function arraySome(array, predicate) {
    var index = -1,
        length = array == null ? 0 : array.length;

    while (++index < length) {
      if (predicate(array[index], index, array)) {
        return true;
      }
    }
    return false;
  }

  /**
   * Gets the size of an ASCII `string`.
   *
   * @private
   * @param {string} string The string inspect.
   * @returns {number} Returns the string size.
   */
  var asciiSize = baseProperty('length');

  /**
   * Converts an ASCII `string` to an array.
   *
   * @private
   * @param {string} string The string to convert.
   * @returns {Array} Returns the converted array.
   */
  function asciiToArray(string) {
    return string.split('');
  }

  /**
   * Splits an ASCII `string` into an array of its words.
   *
   * @private
   * @param {string} The string to inspect.
   * @returns {Array} Returns the words of `string`.
   */
  function asciiWords(string) {
    return string.match(reAsciiWord) || [];
  }

  /**
   * The base implementation of methods like `_.findKey` and `_.findLastKey`,
   * without support for iteratee shorthands, which iterates over `collection`
   * using `eachFunc`.
   *
   * @private
   * @param {Array|Object} collection The collection to inspect.
   * @param {Function} predicate The function invoked per iteration.
   * @param {Function} eachFunc The function to iterate over `collection`.
   * @returns {*} Returns the found element or its key, else `undefined`.
   */
  function baseFindKey(collection, predicate, eachFunc) {
    var result;
    eachFunc(collection, function(value, key, collection) {
      if (predicate(value, key, collection)) {
        result = key;
        return false;
      }
    });
    return result;
  }

  /**
   * The base implementation of `_.findIndex` and `_.findLastIndex` without
   * support for iteratee shorthands.
   *
   * @private
   * @param {Array} array The array to inspect.
   * @param {Function} predicate The function invoked per iteration.
   * @param {number} fromIndex The index to search from.
   * @param {boolean} [fromRight] Specify iterating from right to left.
   * @returns {number} Returns the index of the matched value, else `-1`.
   */
  function baseFindIndex(array, predicate, fromIndex, fromRight) {
    var length = array.length,
        index = fromIndex + (fromRight ? 1 : -1);

    while ((fromRight ? index-- : ++index < length)) {
      if (predicate(array[index], index, array)) {
        return index;
      }
    }
    return -1;
  }

  /**
   * The base implementation of `_.indexOf` without `fromIndex` bounds checks.
   *
   * @private
   * @param {Array} array The array to inspect.
   * @param {*} value The value to search for.
   * @param {number} fromIndex The index to search from.
   * @returns {number} Returns the index of the matched value, else `-1`.
   */
  function baseIndexOf(array, value, fromIndex) {
    return value === value
      ? strictIndexOf(array, value, fromIndex)
      : baseFindIndex(array, baseIsNaN, fromIndex);
  }

  /**
   * This function is like `baseIndexOf` except that it accepts a comparator.
   *
   * @private
   * @param {Array} array The array to inspect.
   * @param {*} value The value to search for.
   * @param {number} fromIndex The index to search from.
   * @param {Function} comparator The comparator invoked per element.
   * @returns {number} Returns the index of the matched value, else `-1`.
   */
  function baseIndexOfWith(array, value, fromIndex, comparator) {
    var index = fromIndex - 1,
        length = array.length;

    while (++index < length) {
      if (comparator(array[index], value)) {
        return index;
      }
    }
    return -1;
  }

  /**
   * The base implementation of `_.isNaN` without support for number objects.
   *
   * @private
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is `NaN`, else `false`.
   */
  function baseIsNaN(value) {
    return value !== value;
  }

  /**
   * The base implementation of `_.mean` and `_.meanBy` without support for
   * iteratee shorthands.
   *
   * @private
   * @param {Array} array The array to iterate over.
   * @param {Function} iteratee The function invoked per iteration.
   * @returns {number} Returns the mean.
   */
  function baseMean(array, iteratee) {
    var length = array == null ? 0 : array.length;
    return length ? (baseSum(array, iteratee) / length) : NAN;
  }

  /**
   * The base implementation of `_.property` without support for deep paths.
   *
   * @private
   * @param {string} key The key of the property to get.
   * @returns {Function} Returns the new accessor function.
   */
  function baseProperty(key) {
    return function(object) {
      return object == null ? undefined : object[key];
    };
  }

  /**
   * The base implementation of `_.propertyOf` without support for deep paths.
   *
   * @private
   * @param {Object} object The object to query.
   * @returns {Function} Returns the new accessor function.
   */
  function basePropertyOf(object) {
    return function(key) {
      return object == null ? undefined : object[key];
    };
  }

  /**
   * The base implementation of `_.reduce` and `_.reduceRight`, without support
   * for iteratee shorthands, which iterates over `collection` using `eachFunc`.
   *
   * @private
   * @param {Array|Object} collection The collection to iterate over.
   * @param {Function} iteratee The function invoked per iteration.
   * @param {*} accumulator The initial value.
   * @param {boolean} initAccum Specify using the first or last element of
   *  `collection` as the initial value.
   * @param {Function} eachFunc The function to iterate over `collection`.
   * @returns {*} Returns the accumulated value.
   */
  function baseReduce(collection, iteratee, accumulator, initAccum, eachFunc) {
    eachFunc(collection, function(value, index, collection) {
      accumulator = initAccum
        ? (initAccum = false, value)
        : iteratee(accumulator, value, index, collection);
    });
    return accumulator;
  }

  /**
   * The base implementation of `_.sortBy` which uses `comparer` to define the
   * sort order of `array` and replaces criteria objects with their corresponding
   * values.
   *
   * @private
   * @param {Array} array The array to sort.
   * @param {Function} comparer The function to define sort order.
   * @returns {Array} Returns `array`.
   */
  function baseSortBy(array, comparer) {
    var length = array.length;

    array.sort(comparer);
    while (length--) {
      array[length] = array[length].value;
    }
    return array;
  }

  /**
   * The base implementation of `_.sum` and `_.sumBy` without support for
   * iteratee shorthands.
   *
   * @private
   * @param {Array} array The array to iterate over.
   * @param {Function} iteratee The function invoked per iteration.
   * @returns {number} Returns the sum.
   */
  function baseSum(array, iteratee) {
    var result,
        index = -1,
        length = array.length;

    while (++index < length) {
      var current = iteratee(array[index]);
      if (current !== undefined) {
        result = result === undefined ? current : (result + current);
      }
    }
    return result;
  }

  /**
   * The base implementation of `_.times` without support for iteratee shorthands
   * or max array length checks.
   *
   * @private
   * @param {number} n The number of times to invoke `iteratee`.
   * @param {Function} iteratee The function invoked per iteration.
   * @returns {Array} Returns the array of results.
   */
  function baseTimes(n, iteratee) {
    var index = -1,
        result = Array(n);

    while (++index < n) {
      result[index] = iteratee(index);
    }
    return result;
  }

  /**
   * The base implementation of `_.toPairs` and `_.toPairsIn` which creates an array
   * of key-value pairs for `object` corresponding to the property names of `props`.
   *
   * @private
   * @param {Object} object The object to query.
   * @param {Array} props The property names to get values for.
   * @returns {Object} Returns the key-value pairs.
   */
  function baseToPairs(object, props) {
    return arrayMap(props, function(key) {
      return [key, object[key]];
    });
  }

  /**
   * The base implementation of `_.trim`.
   *
   * @private
   * @param {string} string The string to trim.
   * @returns {string} Returns the trimmed string.
   */
  function baseTrim(string) {
    return string
      ? string.slice(0, trimmedEndIndex(string) + 1).replace(reTrimStart, '')
      : string;
  }

  /**
   * The base implementation of `_.unary` without support for storing metadata.
   *
   * @private
   * @param {Function} func The function to cap arguments for.
   * @returns {Function} Returns the new capped function.
   */
  function baseUnary(func) {
    return function(value) {
      return func(value);
    };
  }

  /**
   * The base implementation of `_.values` and `_.valuesIn` which creates an
   * array of `object` property values corresponding to the property names
   * of `props`.
   *
   * @private
   * @param {Object} object The object to query.
   * @param {Array} props The property names to get values for.
   * @returns {Object} Returns the array of property values.
   */
  function baseValues(object, props) {
    return arrayMap(props, function(key) {
      return object[key];
    });
  }

  /**
   * Checks if a `cache` value for `key` exists.
   *
   * @private
   * @param {Object} cache The cache to query.
   * @param {string} key The key of the entry to check.
   * @returns {boolean} Returns `true` if an entry for `key` exists, else `false`.
   */
  function cacheHas(cache, key) {
    return cache.has(key);
  }

  /**
   * Used by `_.trim` and `_.trimStart` to get the index of the first string symbol
   * that is not found in the character symbols.
   *
   * @private
   * @param {Array} strSymbols The string symbols to inspect.
   * @param {Array} chrSymbols The character symbols to find.
   * @returns {number} Returns the index of the first unmatched string symbol.
   */
  function charsStartIndex(strSymbols, chrSymbols) {
    var index = -1,
        length = strSymbols.length;

    while (++index < length && baseIndexOf(chrSymbols, strSymbols[index], 0) > -1) {}
    return index;
  }

  /**
   * Used by `_.trim` and `_.trimEnd` to get the index of the last string symbol
   * that is not found in the character symbols.
   *
   * @private
   * @param {Array} strSymbols The string symbols to inspect.
   * @param {Array} chrSymbols The character symbols to find.
   * @returns {number} Returns the index of the last unmatched string symbol.
   */
  function charsEndIndex(strSymbols, chrSymbols) {
    var index = strSymbols.length;

    while (index-- && baseIndexOf(chrSymbols, strSymbols[index], 0) > -1) {}
    return index;
  }

  /**
   * Gets the number of `placeholder` occurrences in `array`.
   *
   * @private
   * @param {Array} array The array to inspect.
   * @param {*} placeholder The placeholder to search for.
   * @returns {number} Returns the placeholder count.
   */
  function countHolders(array, placeholder) {
    var length = array.length,
        result = 0;

    while (length--) {
      if (array[length] === placeholder) {
        ++result;
      }
    }
    return result;
  }

  /**
   * Used by `_.deburr` to convert Latin-1 Supplement and Latin Extended-A
   * letters to basic Latin letters.
   *
   * @private
   * @param {string} letter The matched letter to deburr.
   * @returns {string} Returns the deburred letter.
   */
  var deburrLetter = basePropertyOf(deburredLetters);

  /**
   * Used by `_.escape` to convert characters to HTML entities.
   *
   * @private
   * @param {string} chr The matched character to escape.
   * @returns {string} Returns the escaped character.
   */
  var escapeHtmlChar = basePropertyOf(htmlEscapes);

  /**
   * Used by `_.template` to escape characters for inclusion in compiled string literals.
   *
   * @private
   * @param {string} chr The matched character to escape.
   * @returns {string} Returns the escaped character.
   */
  function escapeStringChar(chr) {
    return '\\' + stringEscapes[chr];
  }

  /**
   * Gets the value at `key` of `object`.
   *
   * @private
   * @param {Object} [object] The object to query.
   * @param {string} key The key of the property to get.
   * @returns {*} Returns the property value.
   */
  function getValue(object, key) {
    return object == null ? undefined : object[key];
  }

  /**
   * Checks if `string` contains Unicode symbols.
   *
   * @private
   * @param {string} string The string to inspect.
   * @returns {boolean} Returns `true` if a symbol is found, else `false`.
   */
  function hasUnicode(string) {
    return reHasUnicode.test(string);
  }

  /**
   * Checks if `string` contains a word composed of Unicode symbols.
   *
   * @private
   * @param {string} string The string to inspect.
   * @returns {boolean} Returns `true` if a word is found, else `false`.
   */
  function hasUnicodeWord(string) {
    return reHasUnicodeWord.test(string);
  }

  /**
   * Converts `iterator` to an array.
   *
   * @private
   * @param {Object} iterator The iterator to convert.
   * @returns {Array} Returns the converted array.
   */
  function iteratorToArray(iterator) {
    var data,
        result = [];

    while (!(data = iterator.next()).done) {
      result.push(data.value);
    }
    return result;
  }

  /**
   * Converts `map` to its key-value pairs.
   *
   * @private
   * @param {Object} map The map to convert.
   * @returns {Array} Returns the key-value pairs.
   */
  function mapToArray(map) {
    var index = -1,
        result = Array(map.size);

    map.forEach(function(value, key) {
      result[++index] = [key, value];
    });
    return result;
  }

  /**
   * Creates a unary function that invokes `func` with its argument transformed.
   *
   * @private
   * @param {Function} func The function to wrap.
   * @param {Function} transform The argument transform.
   * @returns {Function} Returns the new function.
   */
  function overArg(func, transform) {
    return function(arg) {
      return func(transform(arg));
    };
  }

  /**
   * Replaces all `placeholder` elements in `array` with an internal placeholder
   * and returns an array of their indexes.
   *
   * @private
   * @param {Array} array The array to modify.
   * @param {*} placeholder The placeholder to replace.
   * @returns {Array} Returns the new array of placeholder indexes.
   */
  function replaceHolders(array, placeholder) {
    var index = -1,
        length = array.length,
        resIndex = 0,
        result = [];

    while (++index < length) {
      var value = array[index];
      if (value === placeholder || value === PLACEHOLDER) {
        array[index] = PLACEHOLDER;
        result[resIndex++] = index;
      }
    }
    return result;
  }

  /**
   * Converts `set` to an array of its values.
   *
   * @private
   * @param {Object} set The set to convert.
   * @returns {Array} Returns the values.
   */
  function setToArray(set) {
    var index = -1,
        result = Array(set.size);

    set.forEach(function(value) {
      result[++index] = value;
    });
    return result;
  }

  /**
   * Converts `set` to its value-value pairs.
   *
   * @private
   * @param {Object} set The set to convert.
   * @returns {Array} Returns the value-value pairs.
   */
  function setToPairs(set) {
    var index = -1,
        result = Array(set.size);

    set.forEach(function(value) {
      result[++index] = [value, value];
    });
    return result;
  }

  /**
   * A specialized version of `_.indexOf` which performs strict equality
   * comparisons of values, i.e. `===`.
   *
   * @private
   * @param {Array} array The array to inspect.
   * @param {*} value The value to search for.
   * @param {number} fromIndex The index to search from.
   * @returns {number} Returns the index of the matched value, else `-1`.
   */
  function strictIndexOf(array, value, fromIndex) {
    var index = fromIndex - 1,
        length = array.length;

    while (++index < length) {
      if (array[index] === value) {
        return index;
      }
    }
    return -1;
  }

  /**
   * A specialized version of `_.lastIndexOf` which performs strict equality
   * comparisons of values, i.e. `===`.
   *
   * @private
   * @param {Array} array The array to inspect.
   * @param {*} value The value to search for.
   * @param {number} fromIndex The index to search from.
   * @returns {number} Returns the index of the matched value, else `-1`.
   */
  function strictLastIndexOf(array, value, fromIndex) {
    var index = fromIndex + 1;
    while (index--) {
      if (array[index] === value) {
        return index;
      }
    }
    return index;
  }

  /**
   * Gets the number of symbols in `string`.
   *
   * @private
   * @param {string} string The string to inspect.
   * @returns {number} Returns the string size.
   */
  function stringSize(string) {
    return hasUnicode(string)
      ? unicodeSize(string)
      : asciiSize(string);
  }

  /**
   * Converts `string` to an array.
   *
   * @private
   * @param {string} string The string to convert.
   * @returns {Array} Returns the converted array.
   */
  function stringToArray(string) {
    return hasUnicode(string)
      ? unicodeToArray(string)
      : asciiToArray(string);
  }

  /**
   * Used by `_.trim` and `_.trimEnd` to get the index of the last non-whitespace
   * character of `string`.
   *
   * @private
   * @param {string} string The string to inspect.
   * @returns {number} Returns the index of the last non-whitespace character.
   */
  function trimmedEndIndex(string) {
    var index = string.length;

    while (index-- && reWhitespace.test(string.charAt(index))) {}
    return index;
  }

  /**
   * Used by `_.unescape` to convert HTML entities to characters.
   *
   * @private
   * @param {string} chr The matched character to unescape.
   * @returns {string} Returns the unescaped character.
   */
  var unescapeHtmlChar = basePropertyOf(htmlUnescapes);

  /**
   * Gets the size of a Unicode `string`.
   *
   * @private
   * @param {string} string The string inspect.
   * @returns {number} Returns the string size.
   */
  function unicodeSize(string) {
    var result = reUnicode.lastIndex = 0;
    while (reUnicode.test(string)) {
      ++result;
    }
    return result;
  }

  /**
   * Converts a Unicode `string` to an array.
   *
   * @private
   * @param {string} string The string to convert.
   * @returns {Array} Returns the converted array.
   */
  function unicodeToArray(string) {
    return string.match(reUnicode) || [];
  }

  /**
   * Splits a Unicode `string` into an array of its words.
   *
   * @private
   * @param {string} The string to inspect.
   * @returns {Array} Returns the words of `string`.
   */
  function unicodeWords(string) {
    return string.match(reUnicodeWord) || [];
  }

  /*--------------------------------------------------------------------------*/

  /**
   * Create a new pristine `lodash` function using the `context` object.
   *
   * @static
   * @memberOf _
   * @since 1.1.0
   * @category Util
   * @param {Object} [context=root] The context object.
   * @returns {Function} Returns a new `lodash` function.
   * @example
   *
   * _.mixin({ 'foo': _.constant('foo') });
   *
   * var lodash = _.runInContext();
   * lodash.mixin({ 'bar': lodash.constant('bar') });
   *
   * _.isFunction(_.foo);
   * // => true
   * _.isFunction(_.bar);
   * // => false
   *
   * lodash.isFunction(lodash.foo);
   * // => false
   * lodash.isFunction(lodash.bar);
   * // => true
   *
   * // Create a suped-up `defer` in Node.js.
   * var defer = _.runInContext({ 'setTimeout': setImmediate }).defer;
   */
  var runInContext = (function runInContext(context) {
    context = context == null ? root : _.defaults(root.Object(), context, _.pick(root, contextProps));

    /** Built-in constructor references. */
    var Array = context.Array,
        Date = context.Date,
        Error = context.Error,
        Function = context.Function,
        Math = context.Math,
        Object = context.Object,
        RegExp = context.RegExp,
        String = context.String,
        TypeError = context.TypeError;

    /** Used for built-in method references. */
    var arrayProto = Array.prototype,
        funcProto = Function.prototype,
        objectProto = Object.prototype;

    /** Used to detect overreaching core-js shims. */
    var coreJsData = context['__core-js_shared__'];

    /** Used to resolve the decompiled source of functions. */
    var funcToString = funcProto.toString;

    /** Used to check objects for own properties. */
    var hasOwnProperty = objectProto.hasOwnProperty;

    /** Used to generate unique IDs. */
    var idCounter = 0;

    /** Used to detect methods masquerading as native. */
    var maskSrcKey = (function() {
      var uid = /[^.]+$/.exec(coreJsData && coreJsData.keys && coreJsData.keys.IE_PROTO || '');
      return uid ? ('Symbol(src)_1.' + uid) : '';
    }());

    /**
     * Used to resolve the
     * [`toStringTag`](http://ecma-international.org/ecma-262/7.0/#sec-object.prototype.tostring)
     * of values.
     */
    var nativeObjectToString = objectProto.toString;

    /** Used to infer the `Object` constructor. */
    var objectCtorString = funcToString.call(Object);

    /** Used to restore the original `_` reference in `_.noConflict`. */
    var oldDash = root._;

    /** Used to detect if a method is native. */
    var reIsNative = RegExp('^' +
      funcToString.call(hasOwnProperty).replace(reRegExpChar, '\\$&')
      .replace(/hasOwnProperty|(function).*?(?=\\\()| for .+?(?=\\\])/g, '$1.*?') + '$'
    );

    /** Built-in value references. */
    var Buffer = moduleExports ? context.Buffer : undefined,
        Symbol = context.Symbol,
        Uint8Array = context.Uint8Array,
        allocUnsafe = Buffer ? Buffer.allocUnsafe : undefined,
        getPrototype = overArg(Object.getPrototypeOf, Object),
        objectCreate = Object.create,
        propertyIsEnumerable = objectProto.propertyIsEnumerable,
        splice = arrayProto.splice,
        spreadableSymbol = Symbol ? Symbol.isConcatSpreadable : undefined,
        symIterator = Symbol ? Symbol.iterator : undefined,
        symToStringTag = Symbol ? Symbol.toStringTag : undefined;

    var defineProperty = (function() {
      try {
        var func = getNative(Object, 'defineProperty');
        func({}, '', {});
        return func;
      } catch (e) {}
    }());

    /** Mocked built-ins. */
    var ctxClearTimeout = context.clearTimeout !== root.clearTimeout && context.clearTimeout,
        ctxNow = Date && Date.now !== root.Date.now && Date.now,
        ctxSetTimeout = context.setTimeout !== root.setTimeout && context.setTimeout;

    /* Built-in method references for those with the same name as other `lodash` methods. */
    var nativeCeil = Math.ceil,
        nativeFloor = Math.floor,
        nativeGetSymbols = Object.getOwnPropertySymbols,
        nativeIsBuffer = Buffer ? Buffer.isBuffer : undefined,
        nativeIsFinite = context.isFinite,
        nativeJoin = arrayProto.join,
        nativeKeys = overArg(Object.keys, Object),
        nativeMax = Math.max,
        nativeMin = Math.min,
        nativeNow = Date.now,
        nativeParseInt = context.parseInt,
        nativeRandom = Math.random,
        nativeReverse = arrayProto.reverse;

    /* Built-in method references that are verified to be native. */
    var DataView = getNative(context, 'DataView'),
        Map = getNative(context, 'Map'),
        Promise = getNative(context, 'Promise'),
        Set = getNative(context, 'Set'),
        WeakMap = getNative(context, 'WeakMap'),
        nativeCreate = getNative(Object, 'create');

    /** Used to store function metadata. */
    var metaMap = WeakMap && new WeakMap;

    /** Used to lookup unminified function names. */
    var realNames = {};

    /** Used to detect maps, sets, and weakmaps. */
    var dataViewCtorString = toSource(DataView),
        mapCtorString = toSource(Map),
        promiseCtorString = toSource(Promise),
        setCtorString = toSource(Set),
        weakMapCtorString = toSource(WeakMap);

    /** Used to convert symbols to primitives and strings. */
    var symbolProto = Symbol ? Symbol.prototype : undefined,
        symbolValueOf = symbolProto ? symbolProto.valueOf : undefined,
        symbolToString = symbolProto ? symbolProto.toString : undefined;

    /*------------------------------------------------------------------------*/

    /**
     * Creates a `lodash` object which wraps `value` to enable implicit method
     * chain sequences. Methods that operate on and return arrays, collections,
     * and functions can be chained together. Methods that retrieve a single value
     * or may return a primitive value will automatically end the chain sequence
     * and return the unwrapped value. Otherwise, the value must be unwrapped
     * with `_#value`.
     *
     * Explicit chain sequences, which must be unwrapped with `_#value`, may be
     * enabled using `_.chain`.
     *
     * The execution of chained methods is lazy, that is, it's deferred until
     * `_#value` is implicitly or explicitly called.
     *
     * Lazy evaluation allows several methods to support shortcut fusion.
     * Shortcut fusion is an optimization to merge iteratee calls; this avoids
     * the creation of intermediate arrays and can greatly reduce the number of
     * iteratee executions. Sections of a chain sequence qualify for shortcut
     * fusion if the section is applied to an array and iteratees accept only
     * one argument. The heuristic for whether a section qualifies for shortcut
     * fusion is subject to change.
     *
     * Chaining is supported in custom builds as long as the `_#value` method is
     * directly or indirectly included in the build.
     *
     * In addition to lodash methods, wrappers have `Array` and `String` methods.
     *
     * The wrapper `Array` methods are:
     * `concat`, `join`, `pop`, `push`, `shift`, `sort`, `splice`, and `unshift`
     *
     * The wrapper `String` methods are:
     * `replace` and `split`
     *
     * The wrapper methods that support shortcut fusion are:
     * `at`, `compact`, `drop`, `dropRight`, `dropWhile`, `filter`, `find`,
     * `findLast`, `head`, `initial`, `last`, `map`, `reject`, `reverse`, `slice`,
     * `tail`, `take`, `takeRight`, `takeRightWhile`, `takeWhile`, and `toArray`
     *
     * The chainable wrapper methods are:
     * `after`, `ary`, `assign`, `assignIn`, `assignInWith`, `assignWith`, `at`,
     * `before`, `bind`, `bindAll`, `bindKey`, `castArray`, `chain`, `chunk`,
     * `commit`, `compact`, `concat`, `conforms`, `constant`, `countBy`, `create`,
     * `curry`, `debounce`, `defaults`, `defaultsDeep`, `defer`, `delay`,
     * `difference`, `differenceBy`, `differenceWith`, `drop`, `dropRight`,
     * `dropRightWhile`, `dropWhile`, `extend`, `extendWith`, `fill`, `filter`,
     * `flatMap`, `flatMapDeep`, `flatMapDepth`, `flatten`, `flattenDeep`,
     * `flattenDepth`, `flip`, `flow`, `flowRight`, `fromPairs`, `functions`,
     * `functionsIn`, `groupBy`, `initial`, `intersection`, `intersectionBy`,
     * `intersectionWith`, `invert`, `invertBy`, `invokeMap`, `iteratee`, `keyBy`,
     * `keys`, `keysIn`, `map`, `mapKeys`, `mapValues`, `matches`, `matchesProperty`,
     * `memoize`, `merge`, `mergeWith`, `method`, `methodOf`, `mixin`, `negate`,
     * `nthArg`, `omit`, `omitBy`, `once`, `orderBy`, `over`, `overArgs`,
     * `overEvery`, `overSome`, `partial`, `partialRight`, `partition`, `pick`,
     * `pickBy`, `plant`, `property`, `propertyOf`, `pull`, `pullAll`, `pullAllBy`,
     * `pullAllWith`, `pullAt`, `push`, `range`, `rangeRight`, `rearg`, `reject`,
     * `remove`, `rest`, `reverse`, `sampleSize`, `set`, `setWith`, `shuffle`,
     * `slice`, `sort`, `sortBy`, `splice`, `spread`, `tail`, `take`, `takeRight`,
     * `takeRightWhile`, `takeWhile`, `tap`, `throttle`, `thru`, `toArray`,
     * `toPairs`, `toPairsIn`, `toPath`, `toPlainObject`, `transform`, `unary`,
     * `union`, `unionBy`, `unionWith`, `uniq`, `uniqBy`, `uniqWith`, `unset`,
     * `unshift`, `unzip`, `unzipWith`, `update`, `updateWith`, `values`,
     * `valuesIn`, `without`, `wrap`, `xor`, `xorBy`, `xorWith`, `zip`,
     * `zipObject`, `zipObjectDeep`, and `zipWith`
     *
     * The wrapper methods that are **not** chainable by default are:
     * `add`, `attempt`, `camelCase`, `capitalize`, `ceil`, `clamp`, `clone`,
     * `cloneDeep`, `cloneDeepWith`, `cloneWith`, `conformsTo`, `deburr`,
     * `defaultTo`, `divide`, `each`, `eachRight`, `endsWith`, `eq`, `escape`,
     * `escapeRegExp`, `every`, `find`, `findIndex`, `findKey`, `findLast`,
     * `findLastIndex`, `findLastKey`, `first`, `floor`, `forEach`, `forEachRight`,
     * `forIn`, `forInRight`, `forOwn`, `forOwnRight`, `get`, `gt`, `gte`, `has`,
     * `hasIn`, `head`, `identity`, `includes`, `indexOf`, `inRange`, `invoke`,
     * `isArguments`, `isArray`, `isArrayBuffer`, `isArrayLike`, `isArrayLikeObject`,
     * `isBoolean`, `isBuffer`, `isDate`, `isElement`, `isEmpty`, `isEqual`,
     * `isEqualWith`, `isError`, `isFinite`, `isFunction`, `isInteger`, `isLength`,
     * `isMap`, `isMatch`, `isMatchWith`, `isNaN`, `isNative`, `isNil`, `isNull`,
     * `isNumber`, `isObject`, `isObjectLike`, `isPlainObject`, `isRegExp`,
     * `isSafeInteger`, `isSet`, `isString`, `isUndefined`, `isTypedArray`,
     * `isWeakMap`, `isWeakSet`, `join`, `kebabCase`, `last`, `lastIndexOf`,
     * `lowerCase`, `lowerFirst`, `lt`, `lte`, `max`, `maxBy`, `mean`, `meanBy`,
     * `min`, `minBy`, `multiply`, `noConflict`, `noop`, `now`, `nth`, `pad`,
     * `padEnd`, `padStart`, `parseInt`, `pop`, `random`, `reduce`, `reduceRight`,
     * `repeat`, `result`, `round`, `runInContext`, `sample`, `shift`, `size`,
     * `snakeCase`, `some`, `sortedIndex`, `sortedIndexBy`, `sortedLastIndex`,
     * `sortedLastIndexBy`, `startCase`, `startsWith`, `stubArray`, `stubFalse`,
     * `stubObject`, `stubString`, `stubTrue`, `subtract`, `sum`, `sumBy`,
     * `template`, `times`, `toFinite`, `toInteger`, `toJSON`, `toLength`,
     * `toLower`, `toNumber`, `toSafeInteger`, `toString`, `toUpper`, `trim`,
     * `trimEnd`, `trimStart`, `truncate`, `unescape`, `uniqueId`, `upperCase`,
     * `upperFirst`, `value`, and `words`
     *
     * @name _
     * @constructor
     * @category Seq
     * @param {*} value The value to wrap in a `lodash` instance.
     * @returns {Object} Returns the new `lodash` wrapper instance.
     * @example
     *
     * function square(n) {
     *   return n * n;
     * }
     *
     * var wrapped = _([1, 2, 3]);
     *
     * // Returns an unwrapped value.
     * wrapped.reduce(_.add);
     * // => 6
     *
     * // Returns a wrapped value.
     * var squares = wrapped.map(square);
     *
     * _.isArray(squares);
     * // => false
     *
     * _.isArray(squares.value());
     * // => true
     */
    function lodash(value) {
      if (isObjectLike(value) && !isArray(value) && !(value instanceof LazyWrapper)) {
        if (value instanceof LodashWrapper) {
          return value;
        }
        if (hasOwnProperty.call(value, '__wrapped__')) {
          return wrapperClone(value);
        }
      }
      return new LodashWrapper(value);
    }

    /**
     * The base implementation of `_.create` without support for assigning
     * properties to the created object.
     *
     * @private
     * @param {Object} proto The object to inherit from.
     * @returns {Object} Returns the new object.
     */
    var baseCreate = (function() {
      function object() {}
      return function(proto) {
        if (!isObject(proto)) {
          return {};
        }
        if (objectCreate) {
          return objectCreate(proto);
        }
        object.prototype = proto;
        var result = new object;
        object.prototype = undefined;
        return result;
      };
    }());

    /**
     * The function whose prototype chain sequence wrappers inherit from.
     *
     * @private
     */
    function baseLodash() {
      // No operation performed.
    }

    /**
     * The base constructor for creating `lodash` wrapper objects.
     *
     * @private
     * @param {*} value The value to wrap.
     * @param {boolean} [chainAll] Enable explicit method chain sequences.
     */
    function LodashWrapper(value, chainAll) {
      this.__wrapped__ = value;
      this.__actions__ = [];
      this.__chain__ = !!chainAll;
      this.__index__ = 0;
      this.__values__ = undefined;
    }

    /**
     * By default, the template delimiters used by lodash are like those in
     * embedded Ruby (ERB) as well as ES2015 template strings. Change the
     * following template settings to use alternative delimiters.
     *
     * @static
     * @memberOf _
     * @type {Object}
     */
    lodash.templateSettings = {

      /**
       * Used to detect `data` property values to be HTML-escaped.
       *
       * @memberOf _.templateSettings
       * @type {RegExp}
       */
      'escape': reEscape,

      /**
       * Used to detect code to be evaluated.
       *
       * @memberOf _.templateSettings
       * @type {RegExp}
       */
      'evaluate': reEvaluate,

      /**
       * Used to detect `data` property values to inject.
       *
       * @memberOf _.templateSettings
       * @type {RegExp}
       */
      'interpolate': reInterpolate,

      /**
       * Used to reference the data object in the template text.
       *
       * @memberOf _.templateSettings
       * @type {string}
       */
      'variable': '',

      /**
       * Used to import variables into the compiled template.
       *
       * @memberOf _.templateSettings
       * @type {Object}
       */
      'imports': {

        /**
         * A reference to the `lodash` function.
         *
         * @memberOf _.templateSettings.imports
         * @type {Function}
         */
        '_': lodash
      }
    };

    // Ensure wrappers are instances of `baseLodash`.
    lodash.prototype = baseLodash.prototype;
    lodash.prototype.constructor = lodash;

    LodashWrapper.prototype = baseCreate(baseLodash.prototype);
    LodashWrapper.prototype.constructor = LodashWrapper;

    /*------------------------------------------------------------------------*/

    /**
     * Creates a lazy wrapper object which wraps `value` to enable lazy evaluation.
     *
     * @private
     * @constructor
     * @param {*} value The value to wrap.
     */
    function LazyWrapper(value) {
      this.__wrapped__ = value;
      this.__actions__ = [];
      this.__dir__ = 1;
      this.__filtered__ = false;
      this.__iteratees__ = [];
      this.__takeCount__ = MAX_ARRAY_LENGTH;
      this.__views__ = [];
    }

    /**
     * Creates a clone of the lazy wrapper object.
     *
     * @private
     * @name clone
     * @memberOf LazyWrapper
     * @returns {Object} Returns the cloned `LazyWrapper` object.
     */
    function lazyClone() {
      var result = new LazyWrapper(this.__wrapped__);
      result.__actions__ = copyArray(this.__actions__);
      result.__dir__ = this.__dir__;
      result.__filtered__ = this.__filtered__;
      result.__iteratees__ = copyArray(this.__iteratees__);
      result.__takeCount__ = this.__takeCount__;
      result.__views__ = copyArray(this.__views__);
      return result;
    }

    /**
     * Reverses the direction of lazy iteration.
     *
     * @private
     * @name reverse
     * @memberOf LazyWrapper
     * @returns {Object} Returns the new reversed `LazyWrapper` object.
     */
    function lazyReverse() {
      if (this.__filtered__) {
        var result = new LazyWrapper(this);
        result.__dir__ = -1;
        result.__filtered__ = true;
      } else {
        result = this.clone();
        result.__dir__ *= -1;
      }
      return result;
    }

    /**
     * Extracts the unwrapped value from its lazy wrapper.
     *
     * @private
     * @name value
     * @memberOf LazyWrapper
     * @returns {*} Returns the unwrapped value.
     */
    function lazyValue() {
      var array = this.__wrapped__.value(),
          dir = this.__dir__,
          isArr = isArray(array),
          isRight = dir < 0,
          arrLength = isArr ? array.length : 0,
          view = getView(0, arrLength, this.__views__),
          start = view.start,
          end = view.end,
          length = end - start,
          index = isRight ? end : (start - 1),
          iteratees = this.__iteratees__,
          iterLength = iteratees.length,
          resIndex = 0,
          takeCount = nativeMin(length, this.__takeCount__);

      if (!isArr || (!isRight && arrLength == length && takeCount == length)) {
        return baseWrapperValue(array, this.__actions__);
      }
      var result = [];

      outer:
      while (length-- && resIndex < takeCount) {
        index += dir;

        var iterIndex = -1,
            value = array[index];

        while (++iterIndex < iterLength) {
          var data = iteratees[iterIndex],
              iteratee = data.iteratee,
              type = data.type,
              computed = iteratee(value);

          if (type == LAZY_MAP_FLAG) {
            value = computed;
          } else if (!computed) {
            if (type == LAZY_FILTER_FLAG) {
              continue outer;
            } else {
              break outer;
            }
          }
        }
        result[resIndex++] = value;
      }
      return result;
    }

    // Ensure `LazyWrapper` is an instance of `baseLodash`.
    LazyWrapper.prototype = baseCreate(baseLodash.prototype);
    LazyWrapper.prototype.constructor = LazyWrapper;

    /*------------------------------------------------------------------------*/

    /**
     * Creates a hash object.
     *
     * @private
     * @constructor
     * @param {Array} [entries] The key-value pairs to cache.
     */
    function Hash(entries) {
      var index = -1,
          length = entries == null ? 0 : entries.length;

      this.clear();
      while (++index < length) {
        var entry = entries[index];
        this.set(entry[0], entry[1]);
      }
    }

    /**
     * Removes all key-value entries from the hash.
     *
     * @private
     * @name clear
     * @memberOf Hash
     */
    function hashClear() {
      this.__data__ = nativeCreate ? nativeCreate(null) : {};
      this.size = 0;
    }

    /**
     * Removes `key` and its value from the hash.
     *
     * @private
     * @name delete
     * @memberOf Hash
     * @param {Object} hash The hash to modify.
     * @param {string} key The key of the value to remove.
     * @returns {boolean} Returns `true` if the entry was removed, else `false`.
     */
    function hashDelete(key) {
      var result = this.has(key) && delete this.__data__[key];
      this.size -= result ? 1 : 0;
      return result;
    }

    /**
     * Gets the hash value for `key`.
     *
     * @private
     * @name get
     * @memberOf Hash
     * @param {string} key The key of the value to get.
     * @returns {*} Returns the entry value.
     */
    function hashGet(key) {
      var data = this.__data__;
      if (nativeCreate) {
        var result = data[key];
        return result === HASH_UNDEFINED ? undefined : result;
      }
      return hasOwnProperty.call(data, key) ? data[key] : undefined;
    }

    /**
     * Checks if a hash value for `key` exists.
     *
     * @private
     * @name has
     * @memberOf Hash
     * @param {string} key The key of the entry to check.
     * @returns {boolean} Returns `true` if an entry for `key` exists, else `false`.
     */
    function hashHas(key) {
      var data = this.__data__;
      return nativeCreate ? (data[key] !== undefined) : hasOwnProperty.call(data, key);
    }

    /**
     * Sets the hash `key` to `value`.
     *
     * @private
     * @name set
     * @memberOf Hash
     * @param {string} key The key of the value to set.
     * @param {*} value The value to set.
     * @returns {Object} Returns the hash instance.
     */
    function hashSet(key, value) {
      var data = this.__data__;
      this.size += this.has(key) ? 0 : 1;
      data[key] = (nativeCreate && value === undefined) ? HASH_UNDEFINED : value;
      return this;
    }

    // Add methods to `Hash`.
    Hash.prototype.clear = hashClear;
    Hash.prototype['delete'] = hashDelete;
    Hash.prototype.get = hashGet;
    Hash.prototype.has = hashHas;
    Hash.prototype.set = hashSet;

    /*------------------------------------------------------------------------*/

    /**
     * Creates an list cache object.
     *
     * @private
     * @constructor
     * @param {Array} [entries] The key-value pairs to cache.
     */
    function ListCache(entries) {
      var index = -1,
          length = entries == null ? 0 : entries.length;

      this.clear();
      while (++index < length) {
        var entry = entries[index];
        this.set(entry[0], entry[1]);
      }
    }

    /**
     * Removes all key-value entries from the list cache.
     *
     * @private
     * @name clear
     * @memberOf ListCache
     */
    function listCacheClear() {
      this.__data__ = [];
      this.size = 0;
    }

    /**
     * Removes `key` and its value from the list cache.
     *
     * @private
     * @name delete
     * @memberOf ListCache
     * @param {string} key The key of the value to remove.
     * @returns {boolean} Returns `true` if the entry was removed, else `false`.
     */
    function listCacheDelete(key) {
      var data = this.__data__,
          index = assocIndexOf(data, key);

      if (index < 0) {
        return false;
      }
      var lastIndex = data.length - 1;
      if (index == lastIndex) {
        data.pop();
      } else {
        splice.call(data, index, 1);
      }
      --this.size;
      return true;
    }

    /**
     * Gets the list cache value for `key`.
     *
     * @private
     * @name get
     * @memberOf ListCache
     * @param {string} key The key of the value to get.
     * @returns {*} Returns the entry value.
     */
    function listCacheGet(key) {
      var data = this.__data__,
          index = assocIndexOf(data, key);

      return index < 0 ? undefined : data[index][1];
    }

    /**
     * Checks if a list cache value for `key` exists.
     *
     * @private
     * @name has
     * @memberOf ListCache
     * @param {string} key The key of the entry to check.
     * @returns {boolean} Returns `true` if an entry for `key` exists, else `false`.
     */
    function listCacheHas(key) {
      return assocIndexOf(this.__data__, key) > -1;
    }

    /**
     * Sets the list cache `key` to `value`.
     *
     * @private
     * @name set
     * @memberOf ListCache
     * @param {string} key The key of the value to set.
     * @param {*} value The value to set.
     * @returns {Object} Returns the list cache instance.
     */
    function listCacheSet(key, value) {
      var data = this.__data__,
          index = assocIndexOf(data, key);

      if (index < 0) {
        ++this.size;
        data.push([key, value]);
      } else {
        data[index][1] = value;
      }
      return this;
    }

    // Add methods to `ListCache`.
    ListCache.prototype.clear = listCacheClear;
    ListCache.prototype['delete'] = listCacheDelete;
    ListCache.prototype.get = listCacheGet;
    ListCache.prototype.has = listCacheHas;
    ListCache.prototype.set = listCacheSet;

    /*------------------------------------------------------------------------*/

    /**
     * Creates a map cache object to store key-value pairs.
     *
     * @private
     * @constructor
     * @param {Array} [entries] The key-value pairs to cache.
     */
    function MapCache(entries) {
      var index = -1,
          length = entries == null ? 0 : entries.length;

      this.clear();
      while (++index < length) {
        var entry = entries[index];
        this.set(entry[0], entry[1]);
      }
    }

    /**
     * Removes all key-value entries from the map.
     *
     * @private
     * @name clear
     * @memberOf MapCache
     */
    function mapCacheClear() {
      this.size = 0;
      this.__data__ = {
        'hash': new Hash,
        'map': new (Map || ListCache),
        'string': new Hash
      };
    }

    /**
     * Removes `key` and its value from the map.
     *
     * @private
     * @name delete
     * @memberOf MapCache
     * @param {string} key The key of the value to remove.
     * @returns {boolean} Returns `true` if the entry was removed, else `false`.
     */
    function mapCacheDelete(key) {
      var result = getMapData(this, key)['delete'](key);
      this.size -= result ? 1 : 0;
      return result;
    }

    /**
     * Gets the map value for `key`.
     *
     * @private
     * @name get
     * @memberOf MapCache
     * @param {string} key The key of the value to get.
     * @returns {*} Returns the entry value.
     */
    function mapCacheGet(key) {
      return getMapData(this, key).get(key);
    }

    /**
     * Checks if a map value for `key` exists.
     *
     * @private
     * @name has
     * @memberOf MapCache
     * @param {string} key The key of the entry to check.
     * @returns {boolean} Returns `true` if an entry for `key` exists, else `false`.
     */
    function mapCacheHas(key) {
      return getMapData(this, key).has(key);
    }

    /**
     * Sets the map `key` to `value`.
     *
     * @private
     * @name set
     * @memberOf MapCache
     * @param {string} key The key of the value to set.
     * @param {*} value The value to set.
     * @returns {Object} Returns the map cache instance.
     */
    function mapCacheSet(key, value) {
      var data = getMapData(this, key),
          size = data.size;

      data.set(key, value);
      this.size += data.size == size ? 0 : 1;
      return this;
    }

    // Add methods to `MapCache`.
    MapCache.prototype.clear = mapCacheClear;
    MapCache.prototype['delete'] = mapCacheDelete;
    MapCache.prototype.get = mapCacheGet;
    MapCache.prototype.has = mapCacheHas;
    MapCache.prototype.set = mapCacheSet;

    /*------------------------------------------------------------------------*/

    /**
     *
     * Creates an array cache object to store unique values.
     *
     * @private
     * @constructor
     * @param {Array} [values] The values to cache.
     */
    function SetCache(values) {
      var index = -1,
          length = values == null ? 0 : values.length;

      this.__data__ = new MapCache;
      while (++index < length) {
        this.add(values[index]);
      }
    }

    /**
     * Adds `value` to the array cache.
     *
     * @private
     * @name add
     * @memberOf SetCache
     * @alias push
     * @param {*} value The value to cache.
     * @returns {Object} Returns the cache instance.
     */
    function setCacheAdd(value) {
      this.__data__.set(value, HASH_UNDEFINED);
      return this;
    }

    /**
     * Checks if `value` is in the array cache.
     *
     * @private
     * @name has
     * @memberOf SetCache
     * @param {*} value The value to search for.
     * @returns {number} Returns `true` if `value` is found, else `false`.
     */
    function setCacheHas(value) {
      return this.__data__.has(value);
    }

    // Add methods to `SetCache`.
    SetCache.prototype.add = SetCache.prototype.push = setCacheAdd;
    SetCache.prototype.has = setCacheHas;

    /*------------------------------------------------------------------------*/

    /**
     * Creates a stack cache object to store key-value pairs.
     *
     * @private
     * @constructor
     * @param {Array} [entries] The key-value pairs to cache.
     */
    function Stack(entries) {
      var data = this.__data__ = new ListCache(entries);
      this.size = data.size;
    }

    /**
     * Removes all key-value entries from the stack.
     *
     * @private
     * @name clear
     * @memberOf Stack
     */
    function stackClear() {
      this.__data__ = new ListCache;
      this.size = 0;
    }

    /**
     * Removes `key` and its value from the stack.
     *
     * @private
     * @name delete
     * @memberOf Stack
     * @param {string} key The key of the value to remove.
     * @returns {boolean} Returns `true` if the entry was removed, else `false`.
     */
    function stackDelete(key) {
      var data = this.__data__,
          result = data['delete'](key);

      this.size = data.size;
      return result;
    }

    /**
     * Gets the stack value for `key`.
     *
     * @private
     * @name get
     * @memberOf Stack
     * @param {string} key The key of the value to get.
     * @returns {*} Returns the entry value.
     */
    function stackGet(key) {
      return this.__data__.get(key);
    }

    /**
     * Checks if a stack value for `key` exists.
     *
     * @private
     * @name has
     * @memberOf Stack
     * @param {string} key The key of the entry to check.
     * @returns {boolean} Returns `true` if an entry for `key` exists, else `false`.
     */
    function stackHas(key) {
      return this.__data__.has(key);
    }

    /**
     * Sets the stack `key` to `value`.
     *
     * @private
     * @name set
     * @memberOf Stack
     * @param {string} key The key of the value to set.
     * @param {*} value The value to set.
     * @returns {Object} Returns the stack cache instance.
     */
    function stackSet(key, value) {
      var data = this.__data__;
      if (data instanceof ListCache) {
        var pairs = data.__data__;
        if (!Map || (pairs.length < LARGE_ARRAY_SIZE - 1)) {
          pairs.push([key, value]);
          this.size = ++data.size;
          return this;
        }
        data = this.__data__ = new MapCache(pairs);
      }
      data.set(key, value);
      this.size = data.size;
      return this;
    }

    // Add methods to `Stack`.
    Stack.prototype.clear = stackClear;
    Stack.prototype['delete'] = stackDelete;
    Stack.prototype.get = stackGet;
    Stack.prototype.has = stackHas;
    Stack.prototype.set = stackSet;

    /*------------------------------------------------------------------------*/

    /**
     * Creates an array of the enumerable property names of the array-like `value`.
     *
     * @private
     * @param {*} value The value to query.
     * @param {boolean} inherited Specify returning inherited property names.
     * @returns {Array} Returns the array of property names.
     */
    function arrayLikeKeys(value, inherited) {
      var isArr = isArray(value),
          isArg = !isArr && isArguments(value),
          isBuff = !isArr && !isArg && isBuffer(value),
          isType = !isArr && !isArg && !isBuff && isTypedArray(value),
          skipIndexes = isArr || isArg || isBuff || isType,
          result = skipIndexes ? baseTimes(value.length, String) : [],
          length = result.length;

      for (var key in value) {
        if ((inherited || hasOwnProperty.call(value, key)) &&
            !(skipIndexes && (
               // Safari 9 has enumerable `arguments.length` in strict mode.
               key == 'length' ||
               // Node.js 0.10 has enumerable non-index properties on buffers.
               (isBuff && (key == 'offset' || key == 'parent')) ||
               // PhantomJS 2 has enumerable non-index properties on typed arrays.
               (isType && (key == 'buffer' || key == 'byteLength' || key == 'byteOffset')) ||
               // Skip index properties.
               isIndex(key, length)
            ))) {
          result.push(key);
        }
      }
      return result;
    }

    /**
     * A specialized version of `_.sample` for arrays.
     *
     * @private
     * @param {Array} array The array to sample.
     * @returns {*} Returns the random element.
     */
    function arraySample(array) {
      var length = array.length;
      return length ? array[baseRandom(0, length - 1)] : undefined;
    }

    /**
     * A specialized version of `_.sampleSize` for arrays.
     *
     * @private
     * @param {Array} array The array to sample.
     * @param {number} n The number of elements to sample.
     * @returns {Array} Returns the random elements.
     */
    function arraySampleSize(array, n) {
      return shuffleSelf(copyArray(array), baseClamp(n, 0, array.length));
    }

    /**
     * A specialized version of `_.shuffle` for arrays.
     *
     * @private
     * @param {Array} array The array to shuffle.
     * @returns {Array} Returns the new shuffled array.
     */
    function arrayShuffle(array) {
      return shuffleSelf(copyArray(array));
    }

    /**
     * This function is like `assignValue` except that it doesn't assign
     * `undefined` values.
     *
     * @private
     * @param {Object} object The object to modify.
     * @param {string} key The key of the property to assign.
     * @param {*} value The value to assign.
     */
    function assignMergeValue(object, key, value) {
      if ((value !== undefined && !eq(object[key], value)) ||
          (value === undefined && !(key in object))) {
        baseAssignValue(object, key, value);
      }
    }

    /**
     * Assigns `value` to `key` of `object` if the existing value is not equivalent
     * using [`SameValueZero`](http://ecma-international.org/ecma-262/7.0/#sec-samevaluezero)
     * for equality comparisons.
     *
     * @private
     * @param {Object} object The object to modify.
     * @param {string} key The key of the property to assign.
     * @param {*} value The value to assign.
     */
    function assignValue(object, key, value) {
      var objValue = object[key];
      if (!(hasOwnProperty.call(object, key) && eq(objValue, value)) ||
          (value === undefined && !(key in object))) {
        baseAssignValue(object, key, value);
      }
    }

    /**
     * Gets the index at which the `key` is found in `array` of key-value pairs.
     *
     * @private
     * @param {Array} array The array to inspect.
     * @param {*} key The key to search for.
     * @returns {number} Returns the index of the matched value, else `-1`.
     */
    function assocIndexOf(array, key) {
      var length = array.length;
      while (length--) {
        if (eq(array[length][0], key)) {
          return length;
        }
      }
      return -1;
    }

    /**
     * Aggregates elements of `collection` on `accumulator` with keys transformed
     * by `iteratee` and values set by `setter`.
     *
     * @private
     * @param {Array|Object} collection The collection to iterate over.
     * @param {Function} setter The function to set `accumulator` values.
     * @param {Function} iteratee The iteratee to transform keys.
     * @param {Object} accumulator The initial aggregated object.
     * @returns {Function} Returns `accumulator`.
     */
    function baseAggregator(collection, setter, iteratee, accumulator) {
      baseEach(collection, function(value, key, collection) {
        setter(accumulator, value, iteratee(value), collection);
      });
      return accumulator;
    }

    /**
     * The base implementation of `_.assign` without support for multiple sources
     * or `customizer` functions.
     *
     * @private
     * @param {Object} object The destination object.
     * @param {Object} source The source object.
     * @returns {Object} Returns `object`.
     */
    function baseAssign(object, source) {
      return object && copyObject(source, keys(source), object);
    }

    /**
     * The base implementation of `_.assignIn` without support for multiple sources
     * or `customizer` functions.
     *
     * @private
     * @param {Object} object The destination object.
     * @param {Object} source The source object.
     * @returns {Object} Returns `object`.
     */
    function baseAssignIn(object, source) {
      return object && copyObject(source, keysIn(source), object);
    }

    /**
     * The base implementation of `assignValue` and `assignMergeValue` without
     * value checks.
     *
     * @private
     * @param {Object} object The object to modify.
     * @param {string} key The key of the property to assign.
     * @param {*} value The value to assign.
     */
    function baseAssignValue(object, key, value) {
      if (key == '__proto__' && defineProperty) {
        defineProperty(object, key, {
          'configurable': true,
          'enumerable': true,
          'value': value,
          'writable': true
        });
      } else {
        object[key] = value;
      }
    }

    /**
     * The base implementation of `_.at` without support for individual paths.
     *
     * @private
     * @param {Object} object The object to iterate over.
     * @param {string[]} paths The property paths to pick.
     * @returns {Array} Returns the picked elements.
     */
    function baseAt(object, paths) {
      var index = -1,
          length = paths.length,
          result = Array(length),
          skip = object == null;

      while (++index < length) {
        result[index] = skip ? undefined : get(object, paths[index]);
      }
      return result;
    }

    /**
     * The base implementation of `_.clamp` which doesn't coerce arguments.
     *
     * @private
     * @param {number} number The number to clamp.
     * @param {number} [lower] The lower bound.
     * @param {number} upper The upper bound.
     * @returns {number} Returns the clamped number.
     */
    function baseClamp(number, lower, upper) {
      if (number === number) {
        if (upper !== undefined) {
          number = number <= upper ? number : upper;
        }
        if (lower !== undefined) {
          number = number >= lower ? number : lower;
        }
      }
      return number;
    }

    /**
     * The base implementation of `_.clone` and `_.cloneDeep` which tracks
     * traversed objects.
     *
     * @private
     * @param {*} value The value to clone.
     * @param {boolean} bitmask The bitmask flags.
     *  1 - Deep clone
     *  2 - Flatten inherited properties
     *  4 - Clone symbols
     * @param {Function} [customizer] The function to customize cloning.
     * @param {string} [key] The key of `value`.
     * @param {Object} [object] The parent object of `value`.
     * @param {Object} [stack] Tracks traversed objects and their clone counterparts.
     * @returns {*} Returns the cloned value.
     */
    function baseClone(value, bitmask, customizer, key, object, stack) {
      var result,
          isDeep = bitmask & CLONE_DEEP_FLAG,
          isFlat = bitmask & CLONE_FLAT_FLAG,
          isFull = bitmask & CLONE_SYMBOLS_FLAG;

      if (customizer) {
        result = object ? customizer(value, key, object, stack) : customizer(value);
      }
      if (result !== undefined) {
        return result;
      }
      if (!isObject(value)) {
        return value;
      }
      var isArr = isArray(value);
      if (isArr) {
        result = initCloneArray(value);
        if (!isDeep) {
          return copyArray(value, result);
        }
      } else {
        var tag = getTag(value),
            isFunc = tag == funcTag || tag == genTag;

        if (isBuffer(value)) {
          return cloneBuffer(value, isDeep);
        }
        if (tag == objectTag || tag == argsTag || (isFunc && !object)) {
          result = (isFlat || isFunc) ? {} : initCloneObject(value);
          if (!isDeep) {
            return isFlat
              ? copySymbolsIn(value, baseAssignIn(result, value))
              : copySymbols(value, baseAssign(result, value));
          }
        } else {
          if (!cloneableTags[tag]) {
            return object ? value : {};
          }
          result = initCloneByTag(value, tag, isDeep);
        }
      }
      // Check for circular references and return its corresponding clone.
      stack || (stack = new Stack);
      var stacked = stack.get(value);
      if (stacked) {
        return stacked;
      }
      stack.set(value, result);

      if (isSet(value)) {
        value.forEach(function(subValue) {
          result.add(baseClone(subValue, bitmask, customizer, subValue, value, stack));
        });
      } else if (isMap(value)) {
        value.forEach(function(subValue, key) {
          result.set(key, baseClone(subValue, bitmask, customizer, key, value, stack));
        });
      }

      var keysFunc = isFull
        ? (isFlat ? getAllKeysIn : getAllKeys)
        : (isFlat ? keysIn : keys);

      var props = isArr ? undefined : keysFunc(value);
      arrayEach(props || value, function(subValue, key) {
        if (props) {
          key = subValue;
          subValue = value[key];
        }
        // Recursively populate clone (susceptible to call stack limits).
        assignValue(result, key, baseClone(subValue, bitmask, customizer, key, value, stack));
      });
      return result;
    }

    /**
     * The base implementation of `_.conforms` which doesn't clone `source`.
     *
     * @private
     * @param {Object} source The object of property predicates to conform to.
     * @returns {Function} Returns the new spec function.
     */
    function baseConforms(source) {
      var props = keys(source);
      return function(object) {
        return baseConformsTo(object, source, props);
      };
    }

    /**
     * The base implementation of `_.conformsTo` which accepts `props` to check.
     *
     * @private
     * @param {Object} object The object to inspect.
     * @param {Object} source The object of property predicates to conform to.
     * @returns {boolean} Returns `true` if `object` conforms, else `false`.
     */
    function baseConformsTo(object, source, props) {
      var length = props.length;
      if (object == null) {
        return !length;
      }
      object = Object(object);
      while (length--) {
        var key = props[length],
            predicate = source[key],
            value = object[key];

        if ((value === undefined && !(key in object)) || !predicate(value)) {
          return false;
        }
      }
      return true;
    }

    /**
     * The base implementation of `_.delay` and `_.defer` which accepts `args`
     * to provide to `func`.
     *
     * @private
     * @param {Function} func The function to delay.
     * @param {number} wait The number of milliseconds to delay invocation.
     * @param {Array} args The arguments to provide to `func`.
     * @returns {number|Object} Returns the timer id or timeout object.
     */
    function baseDelay(func, wait, args) {
      if (typeof func != 'function') {
        throw new TypeError(FUNC_ERROR_TEXT);
      }
      return setTimeout(function() { func.apply(undefined, args); }, wait);
    }

    /**
     * The base implementation of methods like `_.difference` without support
     * for excluding multiple arrays or iteratee shorthands.
     *
     * @private
     * @param {Array} array The array to inspect.
     * @param {Array} values The values to exclude.
     * @param {Function} [iteratee] The iteratee invoked per element.
     * @param {Function} [comparator] The comparator invoked per element.
     * @returns {Array} Returns the new array of filtered values.
     */
    function baseDifference(array, values, iteratee, comparator) {
      var index = -1,
          includes = arrayIncludes,
          isCommon = true,
          length = array.length,
          result = [],
          valuesLength = values.length;

      if (!length) {
        return result;
      }
      if (iteratee) {
        values = arrayMap(values, baseUnary(iteratee));
      }
      if (comparator) {
        includes = arrayIncludesWith;
        isCommon = false;
      }
      else if (values.length >= LARGE_ARRAY_SIZE) {
        includes = cacheHas;
        isCommon = false;
        values = new SetCache(values);
      }
      outer:
      while (++index < length) {
        var value = array[index],
            computed = iteratee == null ? value : iteratee(value);

        value = (comparator || value !== 0) ? value : 0;
        if (isCommon && computed === computed) {
          var valuesIndex = valuesLength;
          while (valuesIndex--) {
            if (values[valuesIndex] === computed) {
              continue outer;
            }
          }
          result.push(value);
        }
        else if (!includes(values, computed, comparator)) {
          result.push(value);
        }
      }
      return result;
    }

    /**
     * The base implementation of `_.forEach` without support for iteratee shorthands.
     *
     * @private
     * @param {Array|Object} collection The collection to iterate over.
     * @param {Function} iteratee The function invoked per iteration.
     * @returns {Array|Object} Returns `collection`.
     */
    var baseEach = createBaseEach(baseForOwn);

    /**
     * The base implementation of `_.forEachRight` without support for iteratee shorthands.
     *
     * @private
     * @param {Array|Object} collection The collection to iterate over.
     * @param {Function} iteratee The function invoked per iteration.
     * @returns {Array|Object} Returns `collection`.
     */
    var baseEachRight = createBaseEach(baseForOwnRight, true);

    /**
     * The base implementation of `_.every` without support for iteratee shorthands.
     *
     * @private
     * @param {Array|Object} collection The collection to iterate over.
     * @param {Function} predicate The function invoked per iteration.
     * @returns {boolean} Returns `true` if all elements pass the predicate check,
     *  else `false`
     */
    function baseEvery(collection, predicate) {
      var result = true;
      baseEach(collection, function(value, index, collection) {
        result = !!predicate(value, index, collection);
        return result;
      });
      return result;
    }

    /**
     * The base implementation of methods like `_.max` and `_.min` which accepts a
     * `comparator` to determine the extremum value.
     *
     * @private
     * @param {Array} array The array to iterate over.
     * @param {Function} iteratee The iteratee invoked per iteration.
     * @param {Function} comparator The comparator used to compare values.
     * @returns {*} Returns the extremum value.
     */
    function baseExtremum(array, iteratee, comparator) {
      var index = -1,
          length = array.length;

      while (++index < length) {
        var value = array[index],
            current = iteratee(value);

        if (current != null && (computed === undefined
              ? (current === current && !isSymbol(current))
              : comparator(current, computed)
            )) {
          var computed = current,
              result = value;
        }
      }
      return result;
    }

    /**
     * The base implementation of `_.fill` without an iteratee call guard.
     *
     * @private
     * @param {Array} array The array to fill.
     * @param {*} value The value to fill `array` with.
     * @param {number} [start=0] The start position.
     * @param {number} [end=array.length] The end position.
     * @returns {Array} Returns `array`.
     */
    function baseFill(array, value, start, end) {
      var length = array.length;

      start = toInteger(start);
      if (start < 0) {
        start = -start > length ? 0 : (length + start);
      }
      end = (end === undefined || end > length) ? length : toInteger(end);
      if (end < 0) {
        end += length;
      }
      end = start > end ? 0 : toLength(end);
      while (start < end) {
        array[start++] = value;
      }
      return array;
    }

    /**
     * The base implementation of `_.filter` without support for iteratee shorthands.
     *
     * @private
     * @param {Array|Object} collection The collection to iterate over.
     * @param {Function} predicate The function invoked per iteration.
     * @returns {Array} Returns the new filtered array.
     */
    function baseFilter(collection, predicate) {
      var result = [];
      baseEach(collection, function(value, index, collection) {
        if (predicate(value, index, collection)) {
          result.push(value);
        }
      });
      return result;
    }

    /**
     * The base implementation of `_.flatten` with support for restricting flattening.
     *
     * @private
     * @param {Array} array The array to flatten.
     * @param {number} depth The maximum recursion depth.
     * @param {boolean} [predicate=isFlattenable] The function invoked per iteration.
     * @param {boolean} [isStrict] Restrict to values that pass `predicate` checks.
     * @param {Array} [result=[]] The initial result value.
     * @returns {Array} Returns the new flattened array.
     */
    function baseFlatten(array, depth, predicate, isStrict, result) {
      var index = -1,
          length = array.length;

      predicate || (predicate = isFlattenable);
      result || (result = []);

      while (++index < length) {
        var value = array[index];
        if (depth > 0 && predicate(value)) {
          if (depth > 1) {
            // Recursively flatten arrays (susceptible to call stack limits).
            baseFlatten(value, depth - 1, predicate, isStrict, result);
          } else {
            arrayPush(result, value);
          }
        } else if (!isStrict) {
          result[result.length] = value;
        }
      }
      return result;
    }

    /**
     * The base implementation of `baseForOwn` which iterates over `object`
     * properties returned by `keysFunc` and invokes `iteratee` for each property.
     * Iteratee functions may exit iteration early by explicitly returning `false`.
     *
     * @private
     * @param {Object} object The object to iterate over.
     * @param {Function} iteratee The function invoked per iteration.
     * @param {Function} keysFunc The function to get the keys of `object`.
     * @returns {Object} Returns `object`.
     */
    var baseFor = createBaseFor();

    /**
     * This function is like `baseFor` except that it iterates over properties
     * in the opposite order.
     *
     * @private
     * @param {Object} object The object to iterate over.
     * @param {Function} iteratee The function invoked per iteration.
     * @param {Function} keysFunc The function to get the keys of `object`.
     * @returns {Object} Returns `object`.
     */
    var baseForRight = createBaseFor(true);

    /**
     * The base implementation of `_.forOwn` without support for iteratee shorthands.
     *
     * @private
     * @param {Object} object The object to iterate over.
     * @param {Function} iteratee The function invoked per iteration.
     * @returns {Object} Returns `object`.
     */
    function baseForOwn(object, iteratee) {
      return object && baseFor(object, iteratee, keys);
    }

    /**
     * The base implementation of `_.forOwnRight` without support for iteratee shorthands.
     *
     * @private
     * @param {Object} object The object to iterate over.
     * @param {Function} iteratee The function invoked per iteration.
     * @returns {Object} Returns `object`.
     */
    function baseForOwnRight(object, iteratee) {
      return object && baseForRight(object, iteratee, keys);
    }

    /**
     * The base implementation of `_.functions` which creates an array of
     * `object` function property names filtered from `props`.
     *
     * @private
     * @param {Object} object The object to inspect.
     * @param {Array} props The property names to filter.
     * @returns {Array} Returns the function names.
     */
    function baseFunctions(object, props) {
      return arrayFilter(props, function(key) {
        return isFunction(object[key]);
      });
    }

    /**
     * The base implementation of `_.get` without support for default values.
     *
     * @private
     * @param {Object} object The object to query.
     * @param {Array|string} path The path of the property to get.
     * @returns {*} Returns the resolved value.
     */
    function baseGet(object, path) {
      path = castPath(path, object);

      var index = 0,
          length = path.length;

      while (object != null && index < length) {
        object = object[toKey(path[index++])];
      }
      return (index && index == length) ? object : undefined;
    }

    /**
     * The base implementation of `getAllKeys` and `getAllKeysIn` which uses
     * `keysFunc` and `symbolsFunc` to get the enumerable property names and
     * symbols of `object`.
     *
     * @private
     * @param {Object} object The object to query.
     * @param {Function} keysFunc The function to get the keys of `object`.
     * @param {Function} symbolsFunc The function to get the symbols of `object`.
     * @returns {Array} Returns the array of property names and symbols.
     */
    function baseGetAllKeys(object, keysFunc, symbolsFunc) {
      var result = keysFunc(object);
      return isArray(object) ? result : arrayPush(result, symbolsFunc(object));
    }

    /**
     * The base implementation of `getTag` without fallbacks for buggy environments.
     *
     * @private
     * @param {*} value The value to query.
     * @returns {string} Returns the `toStringTag`.
     */
    function baseGetTag(value) {
      if (value == null) {
        return value === undefined ? undefinedTag : nullTag;
      }
      return (symToStringTag && symToStringTag in Object(value))
        ? getRawTag(value)
        : objectToString(value);
    }

    /**
     * The base implementation of `_.gt` which doesn't coerce arguments.
     *
     * @private
     * @param {*} value The value to compare.
     * @param {*} other The other value to compare.
     * @returns {boolean} Returns `true` if `value` is greater than `other`,
     *  else `false`.
     */
    function baseGt(value, other) {
      return value > other;
    }

    /**
     * The base implementation of `_.has` without support for deep paths.
     *
     * @private
     * @param {Object} [object] The object to query.
     * @param {Array|string} key The key to check.
     * @returns {boolean} Returns `true` if `key` exists, else `false`.
     */
    function baseHas(object, key) {
      return object != null && hasOwnProperty.call(object, key);
    }

    /**
     * The base implementation of `_.hasIn` without support for deep paths.
     *
     * @private
     * @param {Object} [object] The object to query.
     * @param {Array|string} key The key to check.
     * @returns {boolean} Returns `true` if `key` exists, else `false`.
     */
    function baseHasIn(object, key) {
      return object != null && key in Object(object);
    }

    /**
     * The base implementation of `_.inRange` which doesn't coerce arguments.
     *
     * @private
     * @param {number} number The number to check.
     * @param {number} start The start of the range.
     * @param {number} end The end of the range.
     * @returns {boolean} Returns `true` if `number` is in the range, else `false`.
     */
    function baseInRange(number, start, end) {
      return number >= nativeMin(start, end) && number < nativeMax(start, end);
    }

    /**
     * The base implementation of methods like `_.intersection`, without support
     * for iteratee shorthands, that accepts an array of arrays to inspect.
     *
     * @private
     * @param {Array} arrays The arrays to inspect.
     * @param {Function} [iteratee] The iteratee invoked per element.
     * @param {Function} [comparator] The comparator invoked per element.
     * @returns {Array} Returns the new array of shared values.
     */
    function baseIntersection(arrays, iteratee, comparator) {
      var includes = comparator ? arrayIncludesWith : arrayIncludes,
          length = arrays[0].length,
          othLength = arrays.length,
          othIndex = othLength,
          caches = Array(othLength),
          maxLength = Infinity,
          result = [];

      while (othIndex--) {
        var array = arrays[othIndex];
        if (othIndex && iteratee) {
          array = arrayMap(array, baseUnary(iteratee));
        }
        maxLength = nativeMin(array.length, maxLength);
        caches[othIndex] = !comparator && (iteratee || (length >= 120 && array.length >= 120))
          ? new SetCache(othIndex && array)
          : undefined;
      }
      array = arrays[0];

      var index = -1,
          seen = caches[0];

      outer:
      while (++index < length && result.length < maxLength) {
        var value = array[index],
            computed = iteratee ? iteratee(value) : value;

        value = (comparator || value !== 0) ? value : 0;
        if (!(seen
              ? cacheHas(seen, computed)
              : includes(result, computed, comparator)
            )) {
          othIndex = othLength;
          while (--othIndex) {
            var cache = caches[othIndex];
            if (!(cache
                  ? cacheHas(cache, computed)
                  : includes(arrays[othIndex], computed, comparator))
                ) {
              continue outer;
            }
          }
          if (seen) {
            seen.push(computed);
          }
          result.push(value);
        }
      }
      return result;
    }

    /**
     * The base implementation of `_.invert` and `_.invertBy` which inverts
     * `object` with values transformed by `iteratee` and set by `setter`.
     *
     * @private
     * @param {Object} object The object to iterate over.
     * @param {Function} setter The function to set `accumulator` values.
     * @param {Function} iteratee The iteratee to transform values.
     * @param {Object} accumulator The initial inverted object.
     * @returns {Function} Returns `accumulator`.
     */
    function baseInverter(object, setter, iteratee, accumulator) {
      baseForOwn(object, function(value, key, object) {
        setter(accumulator, iteratee(value), key, object);
      });
      return accumulator;
    }

    /**
     * The base implementation of `_.invoke` without support for individual
     * method arguments.
     *
     * @private
     * @param {Object} object The object to query.
     * @param {Array|string} path The path of the method to invoke.
     * @param {Array} args The arguments to invoke the method with.
     * @returns {*} Returns the result of the invoked method.
     */
    function baseInvoke(object, path, args) {
      path = castPath(path, object);
      object = parent(object, path);
      var func = object == null ? object : object[toKey(last(path))];
      return func == null ? undefined : apply(func, object, args);
    }

    /**
     * The base implementation of `_.isArguments`.
     *
     * @private
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is an `arguments` object,
     */
    function baseIsArguments(value) {
      return isObjectLike(value) && baseGetTag(value) == argsTag;
    }

    /**
     * The base implementation of `_.isArrayBuffer` without Node.js optimizations.
     *
     * @private
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is an array buffer, else `false`.
     */
    function baseIsArrayBuffer(value) {
      return isObjectLike(value) && baseGetTag(value) == arrayBufferTag;
    }

    /**
     * The base implementation of `_.isDate` without Node.js optimizations.
     *
     * @private
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is a date object, else `false`.
     */
    function baseIsDate(value) {
      return isObjectLike(value) && baseGetTag(value) == dateTag;
    }

    /**
     * The base implementation of `_.isEqual` which supports partial comparisons
     * and tracks traversed objects.
     *
     * @private
     * @param {*} value The value to compare.
     * @param {*} other The other value to compare.
     * @param {boolean} bitmask The bitmask flags.
     *  1 - Unordered comparison
     *  2 - Partial comparison
     * @param {Function} [customizer] The function to customize comparisons.
     * @param {Object} [stack] Tracks traversed `value` and `other` objects.
     * @returns {boolean} Returns `true` if the values are equivalent, else `false`.
     */
    function baseIsEqual(value, other, bitmask, customizer, stack) {
      if (value === other) {
        return true;
      }
      if (value == null || other == null || (!isObjectLike(value) && !isObjectLike(other))) {
        return value !== value && other !== other;
      }
      return baseIsEqualDeep(value, other, bitmask, customizer, baseIsEqual, stack);
    }

    /**
     * A specialized version of `baseIsEqual` for arrays and objects which performs
     * deep comparisons and tracks traversed objects enabling objects with circular
     * references to be compared.
     *
     * @private
     * @param {Object} object The object to compare.
     * @param {Object} other The other object to compare.
     * @param {number} bitmask The bitmask flags. See `baseIsEqual` for more details.
     * @param {Function} customizer The function to customize comparisons.
     * @param {Function} equalFunc The function to determine equivalents of values.
     * @param {Object} [stack] Tracks traversed `object` and `other` objects.
     * @returns {boolean} Returns `true` if the objects are equivalent, else `false`.
     */
    function baseIsEqualDeep(object, other, bitmask, customizer, equalFunc, stack) {
      var objIsArr = isArray(object),
          othIsArr = isArray(other),
          objTag = objIsArr ? arrayTag : getTag(object),
          othTag = othIsArr ? arrayTag : getTag(other);

      objTag = objTag == argsTag ? objectTag : objTag;
      othTag = othTag == argsTag ? objectTag : othTag;

      var objIsObj = objTag == objectTag,
          othIsObj = othTag == objectTag,
          isSameTag = objTag == othTag;

      if (isSameTag && isBuffer(object)) {
        if (!isBuffer(other)) {
          return false;
        }
        objIsArr = true;
        objIsObj = false;
      }
      if (isSameTag && !objIsObj) {
        stack || (stack = new Stack);
        return (objIsArr || isTypedArray(object))
          ? equalArrays(object, other, bitmask, customizer, equalFunc, stack)
          : equalByTag(object, other, objTag, bitmask, customizer, equalFunc, stack);
      }
      if (!(bitmask & COMPARE_PARTIAL_FLAG)) {
        var objIsWrapped = objIsObj && hasOwnProperty.call(object, '__wrapped__'),
            othIsWrapped = othIsObj && hasOwnProperty.call(other, '__wrapped__');

        if (objIsWrapped || othIsWrapped) {
          var objUnwrapped = objIsWrapped ? object.value() : object,
              othUnwrapped = othIsWrapped ? other.value() : other;

          stack || (stack = new Stack);
          return equalFunc(objUnwrapped, othUnwrapped, bitmask, customizer, stack);
        }
      }
      if (!isSameTag) {
        return false;
      }
      stack || (stack = new Stack);
      return equalObjects(object, other, bitmask, customizer, equalFunc, stack);
    }

    /**
     * The base implementation of `_.isMap` without Node.js optimizations.
     *
     * @private
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is a map, else `false`.
     */
    function baseIsMap(value) {
      return isObjectLike(value) && getTag(value) == mapTag;
    }

    /**
     * The base implementation of `_.isMatch` without support for iteratee shorthands.
     *
     * @private
     * @param {Object} object The object to inspect.
     * @param {Object} source The object of property values to match.
     * @param {Array} matchData The property names, values, and compare flags to match.
     * @param {Function} [customizer] The function to customize comparisons.
     * @returns {boolean} Returns `true` if `object` is a match, else `false`.
     */
    function baseIsMatch(object, source, matchData, customizer) {
      var index = matchData.length,
          length = index,
          noCustomizer = !customizer;

      if (object == null) {
        return !length;
      }
      object = Object(object);
      while (index--) {
        var data = matchData[index];
        if ((noCustomizer && data[2])
              ? data[1] !== object[data[0]]
              : !(data[0] in object)
            ) {
          return false;
        }
      }
      while (++index < length) {
        data = matchData[index];
        var key = data[0],
            objValue = object[key],
            srcValue = data[1];

        if (noCustomizer && data[2]) {
          if (objValue === undefined && !(key in object)) {
            return false;
          }
        } else {
          var stack = new Stack;
          if (customizer) {
            var result = customizer(objValue, srcValue, key, object, source, stack);
          }
          if (!(result === undefined
                ? baseIsEqual(srcValue, objValue, COMPARE_PARTIAL_FLAG | COMPARE_UNORDERED_FLAG, customizer, stack)
                : result
              )) {
            return false;
          }
        }
      }
      return true;
    }

    /**
     * The base implementation of `_.isNative` without bad shim checks.
     *
     * @private
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is a native function,
     *  else `false`.
     */
    function baseIsNative(value) {
      if (!isObject(value) || isMasked(value)) {
        return false;
      }
      var pattern = isFunction(value) ? reIsNative : reIsHostCtor;
      return pattern.test(toSource(value));
    }

    /**
     * The base implementation of `_.isRegExp` without Node.js optimizations.
     *
     * @private
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is a regexp, else `false`.
     */
    function baseIsRegExp(value) {
      return isObjectLike(value) && baseGetTag(value) == regexpTag;
    }

    /**
     * The base implementation of `_.isSet` without Node.js optimizations.
     *
     * @private
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is a set, else `false`.
     */
    function baseIsSet(value) {
      return isObjectLike(value) && getTag(value) == setTag;
    }

    /**
     * The base implementation of `_.isTypedArray` without Node.js optimizations.
     *
     * @private
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is a typed array, else `false`.
     */
    function baseIsTypedArray(value) {
      return isObjectLike(value) &&
        isLength(value.length) && !!typedArrayTags[baseGetTag(value)];
    }

    /**
     * The base implementation of `_.iteratee`.
     *
     * @private
     * @param {*} [value=_.identity] The value to convert to an iteratee.
     * @returns {Function} Returns the iteratee.
     */
    function baseIteratee(value) {
      // Don't store the `typeof` result in a variable to avoid a JIT bug in Safari 9.
      // See https://bugs.webkit.org/show_bug.cgi?id=156034 for more details.
      if (typeof value == 'function') {
        return value;
      }
      if (value == null) {
        return identity;
      }
      if (typeof value == 'object') {
        return isArray(value)
          ? baseMatchesProperty(value[0], value[1])
          : baseMatches(value);
      }
      return property(value);
    }

    /**
     * The base implementation of `_.keys` which doesn't treat sparse arrays as dense.
     *
     * @private
     * @param {Object} object The object to query.
     * @returns {Array} Returns the array of property names.
     */
    function baseKeys(object) {
      if (!isPrototype(object)) {
        return nativeKeys(object);
      }
      var result = [];
      for (var key in Object(object)) {
        if (hasOwnProperty.call(object, key) && key != 'constructor') {
          result.push(key);
        }
      }
      return result;
    }

    /**
     * The base implementation of `_.keysIn` which doesn't treat sparse arrays as dense.
     *
     * @private
     * @param {Object} object The object to query.
     * @returns {Array} Returns the array of property names.
     */
    function baseKeysIn(object) {
      if (!isObject(object)) {
        return nativeKeysIn(object);
      }
      var isProto = isPrototype(object),
          result = [];

      for (var key in object) {
        if (!(key == 'constructor' && (isProto || !hasOwnProperty.call(object, key)))) {
          result.push(key);
        }
      }
      return result;
    }

    /**
     * The base implementation of `_.lt` which doesn't coerce arguments.
     *
     * @private
     * @param {*} value The value to compare.
     * @param {*} other The other value to compare.
     * @returns {boolean} Returns `true` if `value` is less than `other`,
     *  else `false`.
     */
    function baseLt(value, other) {
      return value < other;
    }

    /**
     * The base implementation of `_.map` without support for iteratee shorthands.
     *
     * @private
     * @param {Array|Object} collection The collection to iterate over.
     * @param {Function} iteratee The function invoked per iteration.
     * @returns {Array} Returns the new mapped array.
     */
    function baseMap(collection, iteratee) {
      var index = -1,
          result = isArrayLike(collection) ? Array(collection.length) : [];

      baseEach(collection, function(value, key, collection) {
        result[++index] = iteratee(value, key, collection);
      });
      return result;
    }

    /**
     * The base implementation of `_.matches` which doesn't clone `source`.
     *
     * @private
     * @param {Object} source The object of property values to match.
     * @returns {Function} Returns the new spec function.
     */
    function baseMatches(source) {
      var matchData = getMatchData(source);
      if (matchData.length == 1 && matchData[0][2]) {
        return matchesStrictComparable(matchData[0][0], matchData[0][1]);
      }
      return function(object) {
        return object === source || baseIsMatch(object, source, matchData);
      };
    }

    /**
     * The base implementation of `_.matchesProperty` which doesn't clone `srcValue`.
     *
     * @private
     * @param {string} path The path of the property to get.
     * @param {*} srcValue The value to match.
     * @returns {Function} Returns the new spec function.
     */
    function baseMatchesProperty(path, srcValue) {
      if (isKey(path) && isStrictComparable(srcValue)) {
        return matchesStrictComparable(toKey(path), srcValue);
      }
      return function(object) {
        var objValue = get(object, path);
        return (objValue === undefined && objValue === srcValue)
          ? hasIn(object, path)
          : baseIsEqual(srcValue, objValue, COMPARE_PARTIAL_FLAG | COMPARE_UNORDERED_FLAG);
      };
    }

    /**
     * The base implementation of `_.merge` without support for multiple sources.
     *
     * @private
     * @param {Object} object The destination object.
     * @param {Object} source The source object.
     * @param {number} srcIndex The index of `source`.
     * @param {Function} [customizer] The function to customize merged values.
     * @param {Object} [stack] Tracks traversed source values and their merged
     *  counterparts.
     */
    function baseMerge(object, source, srcIndex, customizer, stack) {
      if (object === source) {
        return;
      }
      baseFor(source, function(srcValue, key) {
        stack || (stack = new Stack);
        if (isObject(srcValue)) {
          baseMergeDeep(object, source, key, srcIndex, baseMerge, customizer, stack);
        }
        else {
          var newValue = customizer
            ? customizer(safeGet(object, key), srcValue, (key + ''), object, source, stack)
            : undefined;

          if (newValue === undefined) {
            newValue = srcValue;
          }
          assignMergeValue(object, key, newValue);
        }
      }, keysIn);
    }

    /**
     * A specialized version of `baseMerge` for arrays and objects which performs
     * deep merges and tracks traversed objects enabling objects with circular
     * references to be merged.
     *
     * @private
     * @param {Object} object The destination object.
     * @param {Object} source The source object.
     * @param {string} key The key of the value to merge.
     * @param {number} srcIndex The index of `source`.
     * @param {Function} mergeFunc The function to merge values.
     * @param {Function} [customizer] The function to customize assigned values.
     * @param {Object} [stack] Tracks traversed source values and their merged
     *  counterparts.
     */
    function baseMergeDeep(object, source, key, srcIndex, mergeFunc, customizer, stack) {
      var objValue = safeGet(object, key),
          srcValue = safeGet(source, key),
          stacked = stack.get(srcValue);

      if (stacked) {
        assignMergeValue(object, key, stacked);
        return;
      }
      var newValue = customizer
        ? customizer(objValue, srcValue, (key + ''), object, source, stack)
        : undefined;

      var isCommon = newValue === undefined;

      if (isCommon) {
        var isArr = isArray(srcValue),
            isBuff = !isArr && isBuffer(srcValue),
            isTyped = !isArr && !isBuff && isTypedArray(srcValue);

        newValue = srcValue;
        if (isArr || isBuff || isTyped) {
          if (isArray(objValue)) {
            newValue = objValue;
          }
          else if (isArrayLikeObject(objValue)) {
            newValue = copyArray(objValue);
          }
          else if (isBuff) {
            isCommon = false;
            newValue = cloneBuffer(srcValue, true);
          }
          else if (isTyped) {
            isCommon = false;
            newValue = cloneTypedArray(srcValue, true);
          }
          else {
            newValue = [];
          }
        }
        else if (isPlainObject(srcValue) || isArguments(srcValue)) {
          newValue = objValue;
          if (isArguments(objValue)) {
            newValue = toPlainObject(objValue);
          }
          else if (!isObject(objValue) || isFunction(objValue)) {
            newValue = initCloneObject(srcValue);
          }
        }
        else {
          isCommon = false;
        }
      }
      if (isCommon) {
        // Recursively merge objects and arrays (susceptible to call stack limits).
        stack.set(srcValue, newValue);
        mergeFunc(newValue, srcValue, srcIndex, customizer, stack);
        stack['delete'](srcValue);
      }
      assignMergeValue(object, key, newValue);
    }

    /**
     * The base implementation of `_.nth` which doesn't coerce arguments.
     *
     * @private
     * @param {Array} array The array to query.
     * @param {number} n The index of the element to return.
     * @returns {*} Returns the nth element of `array`.
     */
    function baseNth(array, n) {
      var length = array.length;
      if (!length) {
        return;
      }
      n += n < 0 ? length : 0;
      return isIndex(n, length) ? array[n] : undefined;
    }

    /**
     * The base implementation of `_.orderBy` without param guards.
     *
     * @private
     * @param {Array|Object} collection The collection to iterate over.
     * @param {Function[]|Object[]|string[]} iteratees The iteratees to sort by.
     * @param {string[]} orders The sort orders of `iteratees`.
     * @returns {Array} Returns the new sorted array.
     */
    function baseOrderBy(collection, iteratees, orders) {
      if (iteratees.length) {
        iteratees = arrayMap(iteratees, function(iteratee) {
          if (isArray(iteratee)) {
            return function(value) {
              return baseGet(value, iteratee.length === 1 ? iteratee[0] : iteratee);
            }
          }
          return iteratee;
        });
      } else {
        iteratees = [identity];
      }

      var index = -1;
      iteratees = arrayMap(iteratees, baseUnary(getIteratee()));

      var result = baseMap(collection, function(value, key, collection) {
        var criteria = arrayMap(iteratees, function(iteratee) {
          return iteratee(value);
        });
        return { 'criteria': criteria, 'index': ++index, 'value': value };
      });

      return baseSortBy(result, function(object, other) {
        return compareMultiple(object, other, orders);
      });
    }

    /**
     * The base implementation of `_.pick` without support for individual
     * property identifiers.
     *
     * @private
     * @param {Object} object The source object.
     * @param {string[]} paths The property paths to pick.
     * @returns {Object} Returns the new object.
     */
    function basePick(object, paths) {
      return basePickBy(object, paths, function(value, path) {
        return hasIn(object, path);
      });
    }

    /**
     * The base implementation of  `_.pickBy` without support for iteratee shorthands.
     *
     * @private
     * @param {Object} object The source object.
     * @param {string[]} paths The property paths to pick.
     * @param {Function} predicate The function invoked per property.
     * @returns {Object} Returns the new object.
     */
    function basePickBy(object, paths, predicate) {
      var index = -1,
          length = paths.length,
          result = {};

      while (++index < length) {
        var path = paths[index],
            value = baseGet(object, path);

        if (predicate(value, path)) {
          baseSet(result, castPath(path, object), value);
        }
      }
      return result;
    }

    /**
     * A specialized version of `baseProperty` which supports deep paths.
     *
     * @private
     * @param {Array|string} path The path of the property to get.
     * @returns {Function} Returns the new accessor function.
     */
    function basePropertyDeep(path) {
      return function(object) {
        return baseGet(object, path);
      };
    }

    /**
     * The base implementation of `_.pullAllBy` without support for iteratee
     * shorthands.
     *
     * @private
     * @param {Array} array The array to modify.
     * @param {Array} values The values to remove.
     * @param {Function} [iteratee] The iteratee invoked per element.
     * @param {Function} [comparator] The comparator invoked per element.
     * @returns {Array} Returns `array`.
     */
    function basePullAll(array, values, iteratee, comparator) {
      var indexOf = comparator ? baseIndexOfWith : baseIndexOf,
          index = -1,
          length = values.length,
          seen = array;

      if (array === values) {
        values = copyArray(values);
      }
      if (iteratee) {
        seen = arrayMap(array, baseUnary(iteratee));
      }
      while (++index < length) {
        var fromIndex = 0,
            value = values[index],
            computed = iteratee ? iteratee(value) : value;

        while ((fromIndex = indexOf(seen, computed, fromIndex, comparator)) > -1) {
          if (seen !== array) {
            splice.call(seen, fromIndex, 1);
          }
          splice.call(array, fromIndex, 1);
        }
      }
      return array;
    }

    /**
     * The base implementation of `_.pullAt` without support for individual
     * indexes or capturing the removed elements.
     *
     * @private
     * @param {Array} array The array to modify.
     * @param {number[]} indexes The indexes of elements to remove.
     * @returns {Array} Returns `array`.
     */
    function basePullAt(array, indexes) {
      var length = array ? indexes.length : 0,
          lastIndex = length - 1;

      while (length--) {
        var index = indexes[length];
        if (length == lastIndex || index !== previous) {
          var previous = index;
          if (isIndex(index)) {
            splice.call(array, index, 1);
          } else {
            baseUnset(array, index);
          }
        }
      }
      return array;
    }

    /**
     * The base implementation of `_.random` without support for returning
     * floating-point numbers.
     *
     * @private
     * @param {number} lower The lower bound.
     * @param {number} upper The upper bound.
     * @returns {number} Returns the random number.
     */
    function baseRandom(lower, upper) {
      return lower + nativeFloor(nativeRandom() * (upper - lower + 1));
    }

    /**
     * The base implementation of `_.range` and `_.rangeRight` which doesn't
     * coerce arguments.
     *
     * @private
     * @param {number} start The start of the range.
     * @param {number} end The end of the range.
     * @param {number} step The value to increment or decrement by.
     * @param {boolean} [fromRight] Specify iterating from right to left.
     * @returns {Array} Returns the range of numbers.
     */
    function baseRange(start, end, step, fromRight) {
      var index = -1,
          length = nativeMax(nativeCeil((end - start) / (step || 1)), 0),
          result = Array(length);

      while (length--) {
        result[fromRight ? length : ++index] = start;
        start += step;
      }
      return result;
    }

    /**
     * The base implementation of `_.repeat` which doesn't coerce arguments.
     *
     * @private
     * @param {string} string The string to repeat.
     * @param {number} n The number of times to repeat the string.
     * @returns {string} Returns the repeated string.
     */
    function baseRepeat(string, n) {
      var result = '';
      if (!string || n < 1 || n > MAX_SAFE_INTEGER) {
        return result;
      }
      // Leverage the exponentiation by squaring algorithm for a faster repeat.
      // See https://en.wikipedia.org/wiki/Exponentiation_by_squaring for more details.
      do {
        if (n % 2) {
          result += string;
        }
        n = nativeFloor(n / 2);
        if (n) {
          string += string;
        }
      } while (n);

      return result;
    }

    /**
     * The base implementation of `_.rest` which doesn't validate or coerce arguments.
     *
     * @private
     * @param {Function} func The function to apply a rest parameter to.
     * @param {number} [start=func.length-1] The start position of the rest parameter.
     * @returns {Function} Returns the new function.
     */
    function baseRest(func, start) {
      return setToString(overRest(func, start, identity), func + '');
    }

    /**
     * The base implementation of `_.sample`.
     *
     * @private
     * @param {Array|Object} collection The collection to sample.
     * @returns {*} Returns the random element.
     */
    function baseSample(collection) {
      return arraySample(values(collection));
    }

    /**
     * The base implementation of `_.sampleSize` without param guards.
     *
     * @private
     * @param {Array|Object} collection The collection to sample.
     * @param {number} n The number of elements to sample.
     * @returns {Array} Returns the random elements.
     */
    function baseSampleSize(collection, n) {
      var array = values(collection);
      return shuffleSelf(array, baseClamp(n, 0, array.length));
    }

    /**
     * The base implementation of `_.set`.
     *
     * @private
     * @param {Object} object The object to modify.
     * @param {Array|string} path The path of the property to set.
     * @param {*} value The value to set.
     * @param {Function} [customizer] The function to customize path creation.
     * @returns {Object} Returns `object`.
     */
    function baseSet(object, path, value, customizer) {
      if (!isObject(object)) {
        return object;
      }
      path = castPath(path, object);

      var index = -1,
          length = path.length,
          lastIndex = length - 1,
          nested = object;

      while (nested != null && ++index < length) {
        var key = toKey(path[index]),
            newValue = value;

        if (key === '__proto__' || key === 'constructor' || key === 'prototype') {
          return object;
        }

        if (index != lastIndex) {
          var objValue = nested[key];
          newValue = customizer ? customizer(objValue, key, nested) : undefined;
          if (newValue === undefined) {
            newValue = isObject(objValue)
              ? objValue
              : (isIndex(path[index + 1]) ? [] : {});
          }
        }
        assignValue(nested, key, newValue);
        nested = nested[key];
      }
      return object;
    }

    /**
     * The base implementation of `setData` without support for hot loop shorting.
     *
     * @private
     * @param {Function} func The function to associate metadata with.
     * @param {*} data The metadata.
     * @returns {Function} Returns `func`.
     */
    var baseSetData = !metaMap ? identity : function(func, data) {
      metaMap.set(func, data);
      return func;
    };

    /**
     * The base implementation of `setToString` without support for hot loop shorting.
     *
     * @private
     * @param {Function} func The function to modify.
     * @param {Function} string The `toString` result.
     * @returns {Function} Returns `func`.
     */
    var baseSetToString = !defineProperty ? identity : function(func, string) {
      return defineProperty(func, 'toString', {
        'configurable': true,
        'enumerable': false,
        'value': constant(string),
        'writable': true
      });
    };

    /**
     * The base implementation of `_.shuffle`.
     *
     * @private
     * @param {Array|Object} collection The collection to shuffle.
     * @returns {Array} Returns the new shuffled array.
     */
    function baseShuffle(collection) {
      return shuffleSelf(values(collection));
    }

    /**
     * The base implementation of `_.slice` without an iteratee call guard.
     *
     * @private
     * @param {Array} array The array to slice.
     * @param {number} [start=0] The start position.
     * @param {number} [end=array.length] The end position.
     * @returns {Array} Returns the slice of `array`.
     */
    function baseSlice(array, start, end) {
      var index = -1,
          length = array.length;

      if (start < 0) {
        start = -start > length ? 0 : (length + start);
      }
      end = end > length ? length : end;
      if (end < 0) {
        end += length;
      }
      length = start > end ? 0 : ((end - start) >>> 0);
      start >>>= 0;

      var result = Array(length);
      while (++index < length) {
        result[index] = array[index + start];
      }
      return result;
    }

    /**
     * The base implementation of `_.some` without support for iteratee shorthands.
     *
     * @private
     * @param {Array|Object} collection The collection to iterate over.
     * @param {Function} predicate The function invoked per iteration.
     * @returns {boolean} Returns `true` if any element passes the predicate check,
     *  else `false`.
     */
    function baseSome(collection, predicate) {
      var result;

      baseEach(collection, function(value, index, collection) {
        result = predicate(value, index, collection);
        return !result;
      });
      return !!result;
    }

    /**
     * The base implementation of `_.sortedIndex` and `_.sortedLastIndex` which
     * performs a binary search of `array` to determine the index at which `value`
     * should be inserted into `array` in order to maintain its sort order.
     *
     * @private
     * @param {Array} array The sorted array to inspect.
     * @param {*} value The value to evaluate.
     * @param {boolean} [retHighest] Specify returning the highest qualified index.
     * @returns {number} Returns the index at which `value` should be inserted
     *  into `array`.
     */
    function baseSortedIndex(array, value, retHighest) {
      var low = 0,
          high = array == null ? low : array.length;

      if (typeof value == 'number' && value === value && high <= HALF_MAX_ARRAY_LENGTH) {
        while (low < high) {
          var mid = (low + high) >>> 1,
              computed = array[mid];

          if (computed !== null && !isSymbol(computed) &&
              (retHighest ? (computed <= value) : (computed < value))) {
            low = mid + 1;
          } else {
            high = mid;
          }
        }
        return high;
      }
      return baseSortedIndexBy(array, value, identity, retHighest);
    }

    /**
     * The base implementation of `_.sortedIndexBy` and `_.sortedLastIndexBy`
     * which invokes `iteratee` for `value` and each element of `array` to compute
     * their sort ranking. The iteratee is invoked with one argument; (value).
     *
     * @private
     * @param {Array} array The sorted array to inspect.
     * @param {*} value The value to evaluate.
     * @param {Function} iteratee The iteratee invoked per element.
     * @param {boolean} [retHighest] Specify returning the highest qualified index.
     * @returns {number} Returns the index at which `value` should be inserted
     *  into `array`.
     */
    function baseSortedIndexBy(array, value, iteratee, retHighest) {
      var low = 0,
          high = array == null ? 0 : array.length;
      if (high === 0) {
        return 0;
      }

      value = iteratee(value);
      var valIsNaN = value !== value,
          valIsNull = value === null,
          valIsSymbol = isSymbol(value),
          valIsUndefined = value === undefined;

      while (low < high) {
        var mid = nativeFloor((low + high) / 2),
            computed = iteratee(array[mid]),
            othIsDefined = computed !== undefined,
            othIsNull = computed === null,
            othIsReflexive = computed === computed,
            othIsSymbol = isSymbol(computed);

        if (valIsNaN) {
          var setLow = retHighest || othIsReflexive;
        } else if (valIsUndefined) {
          setLow = othIsReflexive && (retHighest || othIsDefined);
        } else if (valIsNull) {
          setLow = othIsReflexive && othIsDefined && (retHighest || !othIsNull);
        } else if (valIsSymbol) {
          setLow = othIsReflexive && othIsDefined && !othIsNull && (retHighest || !othIsSymbol);
        } else if (othIsNull || othIsSymbol) {
          setLow = false;
        } else {
          setLow = retHighest ? (computed <= value) : (computed < value);
        }
        if (setLow) {
          low = mid + 1;
        } else {
          high = mid;
        }
      }
      return nativeMin(high, MAX_ARRAY_INDEX);
    }

    /**
     * The base implementation of `_.sortedUniq` and `_.sortedUniqBy` without
     * support for iteratee shorthands.
     *
     * @private
     * @param {Array} array The array to inspect.
     * @param {Function} [iteratee] The iteratee invoked per element.
     * @returns {Array} Returns the new duplicate free array.
     */
    function baseSortedUniq(array, iteratee) {
      var index = -1,
          length = array.length,
          resIndex = 0,
          result = [];

      while (++index < length) {
        var value = array[index],
            computed = iteratee ? iteratee(value) : value;

        if (!index || !eq(computed, seen)) {
          var seen = computed;
          result[resIndex++] = value === 0 ? 0 : value;
        }
      }
      return result;
    }

    /**
     * The base implementation of `_.toNumber` which doesn't ensure correct
     * conversions of binary, hexadecimal, or octal string values.
     *
     * @private
     * @param {*} value The value to process.
     * @returns {number} Returns the number.
     */
    function baseToNumber(value) {
      if (typeof value == 'number') {
        return value;
      }
      if (isSymbol(value)) {
        return NAN;
      }
      return +value;
    }

    /**
     * The base implementation of `_.toString` which doesn't convert nullish
     * values to empty strings.
     *
     * @private
     * @param {*} value The value to process.
     * @returns {string} Returns the string.
     */
    function baseToString(value) {
      // Exit early for strings to avoid a performance hit in some environments.
      if (typeof value == 'string') {
        return value;
      }
      if (isArray(value)) {
        // Recursively convert values (susceptible to call stack limits).
        return arrayMap(value, baseToString) + '';
      }
      if (isSymbol(value)) {
        return symbolToString ? symbolToString.call(value) : '';
      }
      var result = (value + '');
      return (result == '0' && (1 / value) == -INFINITY) ? '-0' : result;
    }

    /**
     * The base implementation of `_.uniqBy` without support for iteratee shorthands.
     *
     * @private
     * @param {Array} array The array to inspect.
     * @param {Function} [iteratee] The iteratee invoked per element.
     * @param {Function} [comparator] The comparator invoked per element.
     * @returns {Array} Returns the new duplicate free array.
     */
    function baseUniq(array, iteratee, comparator) {
      var index = -1,
          includes = arrayIncludes,
          length = array.length,
          isCommon = true,
          result = [],
          seen = result;

      if (comparator) {
        isCommon = false;
        includes = arrayIncludesWith;
      }
      else if (length >= LARGE_ARRAY_SIZE) {
        var set = iteratee ? null : createSet(array);
        if (set) {
          return setToArray(set);
        }
        isCommon = false;
        includes = cacheHas;
        seen = new SetCache;
      }
      else {
        seen = iteratee ? [] : result;
      }
      outer:
      while (++index < length) {
        var value = array[index],
            computed = iteratee ? iteratee(value) : value;

        value = (comparator || value !== 0) ? value : 0;
        if (isCommon && computed === computed) {
          var seenIndex = seen.length;
          while (seenIndex--) {
            if (seen[seenIndex] === computed) {
              continue outer;
            }
          }
          if (iteratee) {
            seen.push(computed);
          }
          result.push(value);
        }
        else if (!includes(seen, computed, comparator)) {
          if (seen !== result) {
            seen.push(computed);
          }
          result.push(value);
        }
      }
      return result;
    }

    /**
     * The base implementation of `_.unset`.
     *
     * @private
     * @param {Object} object The object to modify.
     * @param {Array|string} path The property path to unset.
     * @returns {boolean} Returns `true` if the property is deleted, else `false`.
     */
    function baseUnset(object, path) {
      path = castPath(path, object);
      object = parent(object, path);
      return object == null || delete object[toKey(last(path))];
    }

    /**
     * The base implementation of `_.update`.
     *
     * @private
     * @param {Object} object The object to modify.
     * @param {Array|string} path The path of the property to update.
     * @param {Function} updater The function to produce the updated value.
     * @param {Function} [customizer] The function to customize path creation.
     * @returns {Object} Returns `object`.
     */
    function baseUpdate(object, path, updater, customizer) {
      return baseSet(object, path, updater(baseGet(object, path)), customizer);
    }

    /**
     * The base implementation of methods like `_.dropWhile` and `_.takeWhile`
     * without support for iteratee shorthands.
     *
     * @private
     * @param {Array} array The array to query.
     * @param {Function} predicate The function invoked per iteration.
     * @param {boolean} [isDrop] Specify dropping elements instead of taking them.
     * @param {boolean} [fromRight] Specify iterating from right to left.
     * @returns {Array} Returns the slice of `array`.
     */
    function baseWhile(array, predicate, isDrop, fromRight) {
      var length = array.length,
          index = fromRight ? length : -1;

      while ((fromRight ? index-- : ++index < length) &&
        predicate(array[index], index, array)) {}

      return isDrop
        ? baseSlice(array, (fromRight ? 0 : index), (fromRight ? index + 1 : length))
        : baseSlice(array, (fromRight ? index + 1 : 0), (fromRight ? length : index));
    }

    /**
     * The base implementation of `wrapperValue` which returns the result of
     * performing a sequence of actions on the unwrapped `value`, where each
     * successive action is supplied the return value of the previous.
     *
     * @private
     * @param {*} value The unwrapped value.
     * @param {Array} actions Actions to perform to resolve the unwrapped value.
     * @returns {*} Returns the resolved value.
     */
    function baseWrapperValue(value, actions) {
      var result = value;
      if (result instanceof LazyWrapper) {
        result = result.value();
      }
      return arrayReduce(actions, function(result, action) {
        return action.func.apply(action.thisArg, arrayPush([result], action.args));
      }, result);
    }

    /**
     * The base implementation of methods like `_.xor`, without support for
     * iteratee shorthands, that accepts an array of arrays to inspect.
     *
     * @private
     * @param {Array} arrays The arrays to inspect.
     * @param {Function} [iteratee] The iteratee invoked per element.
     * @param {Function} [comparator] The comparator invoked per element.
     * @returns {Array} Returns the new array of values.
     */
    function baseXor(arrays, iteratee, comparator) {
      var length = arrays.length;
      if (length < 2) {
        return length ? baseUniq(arrays[0]) : [];
      }
      var index = -1,
          result = Array(length);

      while (++index < length) {
        var array = arrays[index],
            othIndex = -1;

        while (++othIndex < length) {
          if (othIndex != index) {
            result[index] = baseDifference(result[index] || array, arrays[othIndex], iteratee, comparator);
          }
        }
      }
      return baseUniq(baseFlatten(result, 1), iteratee, comparator);
    }

    /**
     * This base implementation of `_.zipObject` which assigns values using `assignFunc`.
     *
     * @private
     * @param {Array} props The property identifiers.
     * @param {Array} values The property values.
     * @param {Function} assignFunc The function to assign values.
     * @returns {Object} Returns the new object.
     */
    function baseZipObject(props, values, assignFunc) {
      var index = -1,
          length = props.length,
          valsLength = values.length,
          result = {};

      while (++index < length) {
        var value = index < valsLength ? values[index] : undefined;
        assignFunc(result, props[index], value);
      }
      return result;
    }

    /**
     * Casts `value` to an empty array if it's not an array like object.
     *
     * @private
     * @param {*} value The value to inspect.
     * @returns {Array|Object} Returns the cast array-like object.
     */
    function castArrayLikeObject(value) {
      return isArrayLikeObject(value) ? value : [];
    }

    /**
     * Casts `value` to `identity` if it's not a function.
     *
     * @private
     * @param {*} value The value to inspect.
     * @returns {Function} Returns cast function.
     */
    function castFunction(value) {
      return typeof value == 'function' ? value : identity;
    }

    /**
     * Casts `value` to a path array if it's not one.
     *
     * @private
     * @param {*} value The value to inspect.
     * @param {Object} [object] The object to query keys on.
     * @returns {Array} Returns the cast property path array.
     */
    function castPath(value, object) {
      if (isArray(value)) {
        return value;
      }
      return isKey(value, object) ? [value] : stringToPath(toString(value));
    }

    /**
     * A `baseRest` alias which can be replaced with `identity` by module
     * replacement plugins.
     *
     * @private
     * @type {Function}
     * @param {Function} func The function to apply a rest parameter to.
     * @returns {Function} Returns the new function.
     */
    var castRest = baseRest;

    /**
     * Casts `array` to a slice if it's needed.
     *
     * @private
     * @param {Array} array The array to inspect.
     * @param {number} start The start position.
     * @param {number} [end=array.length] The end position.
     * @returns {Array} Returns the cast slice.
     */
    function castSlice(array, start, end) {
      var length = array.length;
      end = end === undefined ? length : end;
      return (!start && end >= length) ? array : baseSlice(array, start, end);
    }

    /**
     * A simple wrapper around the global [`clearTimeout`](https://mdn.io/clearTimeout).
     *
     * @private
     * @param {number|Object} id The timer id or timeout object of the timer to clear.
     */
    var clearTimeout = ctxClearTimeout || function(id) {
      return root.clearTimeout(id);
    };

    /**
     * Creates a clone of  `buffer`.
     *
     * @private
     * @param {Buffer} buffer The buffer to clone.
     * @param {boolean} [isDeep] Specify a deep clone.
     * @returns {Buffer} Returns the cloned buffer.
     */
    function cloneBuffer(buffer, isDeep) {
      if (isDeep) {
        return buffer.slice();
      }
      var length = buffer.length,
          result = allocUnsafe ? allocUnsafe(length) : new buffer.constructor(length);

      buffer.copy(result);
      return result;
    }

    /**
     * Creates a clone of `arrayBuffer`.
     *
     * @private
     * @param {ArrayBuffer} arrayBuffer The array buffer to clone.
     * @returns {ArrayBuffer} Returns the cloned array buffer.
     */
    function cloneArrayBuffer(arrayBuffer) {
      var result = new arrayBuffer.constructor(arrayBuffer.byteLength);
      new Uint8Array(result).set(new Uint8Array(arrayBuffer));
      return result;
    }

    /**
     * Creates a clone of `dataView`.
     *
     * @private
     * @param {Object} dataView The data view to clone.
     * @param {boolean} [isDeep] Specify a deep clone.
     * @returns {Object} Returns the cloned data view.
     */
    function cloneDataView(dataView, isDeep) {
      var buffer = isDeep ? cloneArrayBuffer(dataView.buffer) : dataView.buffer;
      return new dataView.constructor(buffer, dataView.byteOffset, dataView.byteLength);
    }

    /**
     * Creates a clone of `regexp`.
     *
     * @private
     * @param {Object} regexp The regexp to clone.
     * @returns {Object} Returns the cloned regexp.
     */
    function cloneRegExp(regexp) {
      var result = new regexp.constructor(regexp.source, reFlags.exec(regexp));
      result.lastIndex = regexp.lastIndex;
      return result;
    }

    /**
     * Creates a clone of the `symbol` object.
     *
     * @private
     * @param {Object} symbol The symbol object to clone.
     * @returns {Object} Returns the cloned symbol object.
     */
    function cloneSymbol(symbol) {
      return symbolValueOf ? Object(symbolValueOf.call(symbol)) : {};
    }

    /**
     * Creates a clone of `typedArray`.
     *
     * @private
     * @param {Object} typedArray The typed array to clone.
     * @param {boolean} [isDeep] Specify a deep clone.
     * @returns {Object} Returns the cloned typed array.
     */
    function cloneTypedArray(typedArray, isDeep) {
      var buffer = isDeep ? cloneArrayBuffer(typedArray.buffer) : typedArray.buffer;
      return new typedArray.constructor(buffer, typedArray.byteOffset, typedArray.length);
    }

    /**
     * Compares values to sort them in ascending order.
     *
     * @private
     * @param {*} value The value to compare.
     * @param {*} other The other value to compare.
     * @returns {number} Returns the sort order indicator for `value`.
     */
    function compareAscending(value, other) {
      if (value !== other) {
        var valIsDefined = value !== undefined,
            valIsNull = value === null,
            valIsReflexive = value === value,
            valIsSymbol = isSymbol(value);

        var othIsDefined = other !== undefined,
            othIsNull = other === null,
            othIsReflexive = other === other,
            othIsSymbol = isSymbol(other);

        if ((!othIsNull && !othIsSymbol && !valIsSymbol && value > other) ||
            (valIsSymbol && othIsDefined && othIsReflexive && !othIsNull && !othIsSymbol) ||
            (valIsNull && othIsDefined && othIsReflexive) ||
            (!valIsDefined && othIsReflexive) ||
            !valIsReflexive) {
          return 1;
        }
        if ((!valIsNull && !valIsSymbol && !othIsSymbol && value < other) ||
            (othIsSymbol && valIsDefined && valIsReflexive && !valIsNull && !valIsSymbol) ||
            (othIsNull && valIsDefined && valIsReflexive) ||
            (!othIsDefined && valIsReflexive) ||
            !othIsReflexive) {
          return -1;
        }
      }
      return 0;
    }

    /**
     * Used by `_.orderBy` to compare multiple properties of a value to another
     * and stable sort them.
     *
     * If `orders` is unspecified, all values are sorted in ascending order. Otherwise,
     * specify an order of "desc" for descending or "asc" for ascending sort order
     * of corresponding values.
     *
     * @private
     * @param {Object} object The object to compare.
     * @param {Object} other The other object to compare.
     * @param {boolean[]|string[]} orders The order to sort by for each property.
     * @returns {number} Returns the sort order indicator for `object`.
     */
    function compareMultiple(object, other, orders) {
      var index = -1,
          objCriteria = object.criteria,
          othCriteria = other.criteria,
          length = objCriteria.length,
          ordersLength = orders.length;

      while (++index < length) {
        var result = compareAscending(objCriteria[index], othCriteria[index]);
        if (result) {
          if (index >= ordersLength) {
            return result;
          }
          var order = orders[index];
          return result * (order == 'desc' ? -1 : 1);
        }
      }
      // Fixes an `Array#sort` bug in the JS engine embedded in Adobe applications
      // that causes it, under certain circumstances, to provide the same value for
      // `object` and `other`. See https://github.com/jashkenas/underscore/pull/1247
      // for more details.
      //
      // This also ensures a stable sort in V8 and other engines.
      // See https://bugs.chromium.org/p/v8/issues/detail?id=90 for more details.
      return object.index - other.index;
    }

    /**
     * Creates an array that is the composition of partially applied arguments,
     * placeholders, and provided arguments into a single array of arguments.
     *
     * @private
     * @param {Array} args The provided arguments.
     * @param {Array} partials The arguments to prepend to those provided.
     * @param {Array} holders The `partials` placeholder indexes.
     * @params {boolean} [isCurried] Specify composing for a curried function.
     * @returns {Array} Returns the new array of composed arguments.
     */
    function composeArgs(args, partials, holders, isCurried) {
      var argsIndex = -1,
          argsLength = args.length,
          holdersLength = holders.length,
          leftIndex = -1,
          leftLength = partials.length,
          rangeLength = nativeMax(argsLength - holdersLength, 0),
          result = Array(leftLength + rangeLength),
          isUncurried = !isCurried;

      while (++leftIndex < leftLength) {
        result[leftIndex] = partials[leftIndex];
      }
      while (++argsIndex < holdersLength) {
        if (isUncurried || argsIndex < argsLength) {
          result[holders[argsIndex]] = args[argsIndex];
        }
      }
      while (rangeLength--) {
        result[leftIndex++] = args[argsIndex++];
      }
      return result;
    }

    /**
     * This function is like `composeArgs` except that the arguments composition
     * is tailored for `_.partialRight`.
     *
     * @private
     * @param {Array} args The provided arguments.
     * @param {Array} partials The arguments to append to those provided.
     * @param {Array} holders The `partials` placeholder indexes.
     * @params {boolean} [isCurried] Specify composing for a curried function.
     * @returns {Array} Returns the new array of composed arguments.
     */
    function composeArgsRight(args, partials, holders, isCurried) {
      var argsIndex = -1,
          argsLength = args.length,
          holdersIndex = -1,
          holdersLength = holders.length,
          rightIndex = -1,
          rightLength = partials.length,
          rangeLength = nativeMax(argsLength - holdersLength, 0),
          result = Array(rangeLength + rightLength),
          isUncurried = !isCurried;

      while (++argsIndex < rangeLength) {
        result[argsIndex] = args[argsIndex];
      }
      var offset = argsIndex;
      while (++rightIndex < rightLength) {
        result[offset + rightIndex] = partials[rightIndex];
      }
      while (++holdersIndex < holdersLength) {
        if (isUncurried || argsIndex < argsLength) {
          result[offset + holders[holdersIndex]] = args[argsIndex++];
        }
      }
      return result;
    }

    /**
     * Copies the values of `source` to `array`.
     *
     * @private
     * @param {Array} source The array to copy values from.
     * @param {Array} [array=[]] The array to copy values to.
     * @returns {Array} Returns `array`.
     */
    function copyArray(source, array) {
      var index = -1,
          length = source.length;

      array || (array = Array(length));
      while (++index < length) {
        array[index] = source[index];
      }
      return array;
    }

    /**
     * Copies properties of `source` to `object`.
     *
     * @private
     * @param {Object} source The object to copy properties from.
     * @param {Array} props The property identifiers to copy.
     * @param {Object} [object={}] The object to copy properties to.
     * @param {Function} [customizer] The function to customize copied values.
     * @returns {Object} Returns `object`.
     */
    function copyObject(source, props, object, customizer) {
      var isNew = !object;
      object || (object = {});

      var index = -1,
          length = props.length;

      while (++index < length) {
        var key = props[index];

        var newValue = customizer
          ? customizer(object[key], source[key], key, object, source)
          : undefined;

        if (newValue === undefined) {
          newValue = source[key];
        }
        if (isNew) {
          baseAssignValue(object, key, newValue);
        } else {
          assignValue(object, key, newValue);
        }
      }
      return object;
    }

    /**
     * Copies own symbols of `source` to `object`.
     *
     * @private
     * @param {Object} source The object to copy symbols from.
     * @param {Object} [object={}] The object to copy symbols to.
     * @returns {Object} Returns `object`.
     */
    function copySymbols(source, object) {
      return copyObject(source, getSymbols(source), object);
    }

    /**
     * Copies own and inherited symbols of `source` to `object`.
     *
     * @private
     * @param {Object} source The object to copy symbols from.
     * @param {Object} [object={}] The object to copy symbols to.
     * @returns {Object} Returns `object`.
     */
    function copySymbolsIn(source, object) {
      return copyObject(source, getSymbolsIn(source), object);
    }

    /**
     * Creates a function like `_.groupBy`.
     *
     * @private
     * @param {Function} setter The function to set accumulator values.
     * @param {Function} [initializer] The accumulator object initializer.
     * @returns {Function} Returns the new aggregator function.
     */
    function createAggregator(setter, initializer) {
      return function(collection, iteratee) {
        var func = isArray(collection) ? arrayAggregator : baseAggregator,
            accumulator = initializer ? initializer() : {};

        return func(collection, setter, getIteratee(iteratee, 2), accumulator);
      };
    }

    /**
     * Creates a function like `_.assign`.
     *
     * @private
     * @param {Function} assigner The function to assign values.
     * @returns {Function} Returns the new assigner function.
     */
    function createAssigner(assigner) {
      return baseRest(function(object, sources) {
        var index = -1,
            length = sources.length,
            customizer = length > 1 ? sources[length - 1] : undefined,
            guard = length > 2 ? sources[2] : undefined;

        customizer = (assigner.length > 3 && typeof customizer == 'function')
          ? (length--, customizer)
          : undefined;

        if (guard && isIterateeCall(sources[0], sources[1], guard)) {
          customizer = length < 3 ? undefined : customizer;
          length = 1;
        }
        object = Object(object);
        while (++index < length) {
          var source = sources[index];
          if (source) {
            assigner(object, source, index, customizer);
          }
        }
        return object;
      });
    }

    /**
     * Creates a `baseEach` or `baseEachRight` function.
     *
     * @private
     * @param {Function} eachFunc The function to iterate over a collection.
     * @param {boolean} [fromRight] Specify iterating from right to left.
     * @returns {Function} Returns the new base function.
     */
    function createBaseEach(eachFunc, fromRight) {
      return function(collection, iteratee) {
        if (collection == null) {
          return collection;
        }
        if (!isArrayLike(collection)) {
          return eachFunc(collection, iteratee);
        }
        var length = collection.length,
            index = fromRight ? length : -1,
            iterable = Object(collection);

        while ((fromRight ? index-- : ++index < length)) {
          if (iteratee(iterable[index], index, iterable) === false) {
            break;
          }
        }
        return collection;
      };
    }

    /**
     * Creates a base function for methods like `_.forIn` and `_.forOwn`.
     *
     * @private
     * @param {boolean} [fromRight] Specify iterating from right to left.
     * @returns {Function} Returns the new base function.
     */
    function createBaseFor(fromRight) {
      return function(object, iteratee, keysFunc) {
        var index = -1,
            iterable = Object(object),
            props = keysFunc(object),
            length = props.length;

        while (length--) {
          var key = props[fromRight ? length : ++index];
          if (iteratee(iterable[key], key, iterable) === false) {
            break;
          }
        }
        return object;
      };
    }

    /**
     * Creates a function that wraps `func` to invoke it with the optional `this`
     * binding of `thisArg`.
     *
     * @private
     * @param {Function} func The function to wrap.
     * @param {number} bitmask The bitmask flags. See `createWrap` for more details.
     * @param {*} [thisArg] The `this` binding of `func`.
     * @returns {Function} Returns the new wrapped function.
     */
    function createBind(func, bitmask, thisArg) {
      var isBind = bitmask & WRAP_BIND_FLAG,
          Ctor = createCtor(func);

      function wrapper() {
        var fn = (this && this !== root && this instanceof wrapper) ? Ctor : func;
        return fn.apply(isBind ? thisArg : this, arguments);
      }
      return wrapper;
    }

    /**
     * Creates a function like `_.lowerFirst`.
     *
     * @private
     * @param {string} methodName The name of the `String` case method to use.
     * @returns {Function} Returns the new case function.
     */
    function createCaseFirst(methodName) {
      return function(string) {
        string = toString(string);

        var strSymbols = hasUnicode(string)
          ? stringToArray(string)
          : undefined;

        var chr = strSymbols
          ? strSymbols[0]
          : string.charAt(0);

        var trailing = strSymbols
          ? castSlice(strSymbols, 1).join('')
          : string.slice(1);

        return chr[methodName]() + trailing;
      };
    }

    /**
     * Creates a function like `_.camelCase`.
     *
     * @private
     * @param {Function} callback The function to combine each word.
     * @returns {Function} Returns the new compounder function.
     */
    function createCompounder(callback) {
      return function(string) {
        return arrayReduce(words(deburr(string).replace(reApos, '')), callback, '');
      };
    }

    /**
     * Creates a function that produces an instance of `Ctor` regardless of
     * whether it was invoked as part of a `new` expression or by `call` or `apply`.
     *
     * @private
     * @param {Function} Ctor The constructor to wrap.
     * @returns {Function} Returns the new wrapped function.
     */
    function createCtor(Ctor) {
      return function() {
        // Use a `switch` statement to work with class constructors. See
        // http://ecma-international.org/ecma-262/7.0/#sec-ecmascript-function-objects-call-thisargument-argumentslist
        // for more details.
        var args = arguments;
        switch (args.length) {
          case 0: return new Ctor;
          case 1: return new Ctor(args[0]);
          case 2: return new Ctor(args[0], args[1]);
          case 3: return new Ctor(args[0], args[1], args[2]);
          case 4: return new Ctor(args[0], args[1], args[2], args[3]);
          case 5: return new Ctor(args[0], args[1], args[2], args[3], args[4]);
          case 6: return new Ctor(args[0], args[1], args[2], args[3], args[4], args[5]);
          case 7: return new Ctor(args[0], args[1], args[2], args[3], args[4], args[5], args[6]);
        }
        var thisBinding = baseCreate(Ctor.prototype),
            result = Ctor.apply(thisBinding, args);

        // Mimic the constructor's `return` behavior.
        // See https://es5.github.io/#x13.2.2 for more details.
        return isObject(result) ? result : thisBinding;
      };
    }

    /**
     * Creates a function that wraps `func` to enable currying.
     *
     * @private
     * @param {Function} func The function to wrap.
     * @param {number} bitmask The bitmask flags. See `createWrap` for more details.
     * @param {number} arity The arity of `func`.
     * @returns {Function} Returns the new wrapped function.
     */
    function createCurry(func, bitmask, arity) {
      var Ctor = createCtor(func);

      function wrapper() {
        var length = arguments.length,
            args = Array(length),
            index = length,
            placeholder = getHolder(wrapper);

        while (index--) {
          args[index] = arguments[index];
        }
        var holders = (length < 3 && args[0] !== placeholder && args[length - 1] !== placeholder)
          ? []
          : replaceHolders(args, placeholder);

        length -= holders.length;
        if (length < arity) {
          return createRecurry(
            func, bitmask, createHybrid, wrapper.placeholder, undefined,
            args, holders, undefined, undefined, arity - length);
        }
        var fn = (this && this !== root && this instanceof wrapper) ? Ctor : func;
        return apply(fn, this, args);
      }
      return wrapper;
    }

    /**
     * Creates a `_.find` or `_.findLast` function.
     *
     * @private
     * @param {Function} findIndexFunc The function to find the collection index.
     * @returns {Function} Returns the new find function.
     */
    function createFind(findIndexFunc) {
      return function(collection, predicate, fromIndex) {
        var iterable = Object(collection);
        if (!isArrayLike(collection)) {
          var iteratee = getIteratee(predicate, 3);
          collection = keys(collection);
          predicate = function(key) { return iteratee(iterable[key], key, iterable); };
        }
        var index = findIndexFunc(collection, predicate, fromIndex);
        return index > -1 ? iterable[iteratee ? collection[index] : index] : undefined;
      };
    }

    /**
     * Creates a `_.flow` or `_.flowRight` function.
     *
     * @private
     * @param {boolean} [fromRight] Specify iterating from right to left.
     * @returns {Function} Returns the new flow function.
     */
    function createFlow(fromRight) {
      return flatRest(function(funcs) {
        var length = funcs.length,
            index = length,
            prereq = LodashWrapper.prototype.thru;

        if (fromRight) {
          funcs.reverse();
        }
        while (index--) {
          var func = funcs[index];
          if (typeof func != 'function') {
            throw new TypeError(FUNC_ERROR_TEXT);
          }
          if (prereq && !wrapper && getFuncName(func) == 'wrapper') {
            var wrapper = new LodashWrapper([], true);
          }
        }
        index = wrapper ? index : length;
        while (++index < length) {
          func = funcs[index];

          var funcName = getFuncName(func),
              data = funcName == 'wrapper' ? getData(func) : undefined;

          if (data && isLaziable(data[0]) &&
                data[1] == (WRAP_ARY_FLAG | WRAP_CURRY_FLAG | WRAP_PARTIAL_FLAG | WRAP_REARG_FLAG) &&
                !data[4].length && data[9] == 1
              ) {
            wrapper = wrapper[getFuncName(data[0])].apply(wrapper, data[3]);
          } else {
            wrapper = (func.length == 1 && isLaziable(func))
              ? wrapper[funcName]()
              : wrapper.thru(func);
          }
        }
        return function() {
          var args = arguments,
              value = args[0];

          if (wrapper && args.length == 1 && isArray(value)) {
            return wrapper.plant(value).value();
          }
          var index = 0,
              result = length ? funcs[index].apply(this, args) : value;

          while (++index < length) {
            result = funcs[index].call(this, result);
          }
          return result;
        };
      });
    }

    /**
     * Creates a function that wraps `func` to invoke it with optional `this`
     * binding of `thisArg`, partial application, and currying.
     *
     * @private
     * @param {Function|string} func The function or method name to wrap.
     * @param {number} bitmask The bitmask flags. See `createWrap` for more details.
     * @param {*} [thisArg] The `this` binding of `func`.
     * @param {Array} [partials] The arguments to prepend to those provided to
     *  the new function.
     * @param {Array} [holders] The `partials` placeholder indexes.
     * @param {Array} [partialsRight] The arguments to append to those provided
     *  to the new function.
     * @param {Array} [holdersRight] The `partialsRight` placeholder indexes.
     * @param {Array} [argPos] The argument positions of the new function.
     * @param {number} [ary] The arity cap of `func`.
     * @param {number} [arity] The arity of `func`.
     * @returns {Function} Returns the new wrapped function.
     */
    function createHybrid(func, bitmask, thisArg, partials, holders, partialsRight, holdersRight, argPos, ary, arity) {
      var isAry = bitmask & WRAP_ARY_FLAG,
          isBind = bitmask & WRAP_BIND_FLAG,
          isBindKey = bitmask & WRAP_BIND_KEY_FLAG,
          isCurried = bitmask & (WRAP_CURRY_FLAG | WRAP_CURRY_RIGHT_FLAG),
          isFlip = bitmask & WRAP_FLIP_FLAG,
          Ctor = isBindKey ? undefined : createCtor(func);

      function wrapper() {
        var length = arguments.length,
            args = Array(length),
            index = length;

        while (index--) {
          args[index] = arguments[index];
        }
        if (isCurried) {
          var placeholder = getHolder(wrapper),
              holdersCount = countHolders(args, placeholder);
        }
        if (partials) {
          args = composeArgs(args, partials, holders, isCurried);
        }
        if (partialsRight) {
          args = composeArgsRight(args, partialsRight, holdersRight, isCurried);
        }
        length -= holdersCount;
        if (isCurried && length < arity) {
          var newHolders = replaceHolders(args, placeholder);
          return createRecurry(
            func, bitmask, createHybrid, wrapper.placeholder, thisArg,
            args, newHolders, argPos, ary, arity - length
          );
        }
        var thisBinding = isBind ? thisArg : this,
            fn = isBindKey ? thisBinding[func] : func;

        length = args.length;
        if (argPos) {
          args = reorder(args, argPos);
        } else if (isFlip && length > 1) {
          args.reverse();
        }
        if (isAry && ary < length) {
          args.length = ary;
        }
        if (this && this !== root && this instanceof wrapper) {
          fn = Ctor || createCtor(fn);
        }
        return fn.apply(thisBinding, args);
      }
      return wrapper;
    }

    /**
     * Creates a function like `_.invertBy`.
     *
     * @private
     * @param {Function} setter The function to set accumulator values.
     * @param {Function} toIteratee The function to resolve iteratees.
     * @returns {Function} Returns the new inverter function.
     */
    function createInverter(setter, toIteratee) {
      return function(object, iteratee) {
        return baseInverter(object, setter, toIteratee(iteratee), {});
      };
    }

    /**
     * Creates a function that performs a mathematical operation on two values.
     *
     * @private
     * @param {Function} operator The function to perform the operation.
     * @param {number} [defaultValue] The value used for `undefined` arguments.
     * @returns {Function} Returns the new mathematical operation function.
     */
    function createMathOperation(operator, defaultValue) {
      return function(value, other) {
        var result;
        if (value === undefined && other === undefined) {
          return defaultValue;
        }
        if (value !== undefined) {
          result = value;
        }
        if (other !== undefined) {
          if (result === undefined) {
            return other;
          }
          if (typeof value == 'string' || typeof other == 'string') {
            value = baseToString(value);
            other = baseToString(other);
          } else {
            value = baseToNumber(value);
            other = baseToNumber(other);
          }
          result = operator(value, other);
        }
        return result;
      };
    }

    /**
     * Creates a function like `_.over`.
     *
     * @private
     * @param {Function} arrayFunc The function to iterate over iteratees.
     * @returns {Function} Returns the new over function.
     */
    function createOver(arrayFunc) {
      return flatRest(function(iteratees) {
        iteratees = arrayMap(iteratees, baseUnary(getIteratee()));
        return baseRest(function(args) {
          var thisArg = this;
          return arrayFunc(iteratees, function(iteratee) {
            return apply(iteratee, thisArg, args);
          });
        });
      });
    }

    /**
     * Creates the padding for `string` based on `length`. The `chars` string
     * is truncated if the number of characters exceeds `length`.
     *
     * @private
     * @param {number} length The padding length.
     * @param {string} [chars=' '] The string used as padding.
     * @returns {string} Returns the padding for `string`.
     */
    function createPadding(length, chars) {
      chars = chars === undefined ? ' ' : baseToString(chars);

      var charsLength = chars.length;
      if (charsLength < 2) {
        return charsLength ? baseRepeat(chars, length) : chars;
      }
      var result = baseRepeat(chars, nativeCeil(length / stringSize(chars)));
      return hasUnicode(chars)
        ? castSlice(stringToArray(result), 0, length).join('')
        : result.slice(0, length);
    }

    /**
     * Creates a function that wraps `func` to invoke it with the `this` binding
     * of `thisArg` and `partials` prepended to the arguments it receives.
     *
     * @private
     * @param {Function} func The function to wrap.
     * @param {number} bitmask The bitmask flags. See `createWrap` for more details.
     * @param {*} thisArg The `this` binding of `func`.
     * @param {Array} partials The arguments to prepend to those provided to
     *  the new function.
     * @returns {Function} Returns the new wrapped function.
     */
    function createPartial(func, bitmask, thisArg, partials) {
      var isBind = bitmask & WRAP_BIND_FLAG,
          Ctor = createCtor(func);

      function wrapper() {
        var argsIndex = -1,
            argsLength = arguments.length,
            leftIndex = -1,
            leftLength = partials.length,
            args = Array(leftLength + argsLength),
            fn = (this && this !== root && this instanceof wrapper) ? Ctor : func;

        while (++leftIndex < leftLength) {
          args[leftIndex] = partials[leftIndex];
        }
        while (argsLength--) {
          args[leftIndex++] = arguments[++argsIndex];
        }
        return apply(fn, isBind ? thisArg : this, args);
      }
      return wrapper;
    }

    /**
     * Creates a `_.range` or `_.rangeRight` function.
     *
     * @private
     * @param {boolean} [fromRight] Specify iterating from right to left.
     * @returns {Function} Returns the new range function.
     */
    function createRange(fromRight) {
      return function(start, end, step) {
        if (step && typeof step != 'number' && isIterateeCall(start, end, step)) {
          end = step = undefined;
        }
        // Ensure the sign of `-0` is preserved.
        start = toFinite(start);
        if (end === undefined) {
          end = start;
          start = 0;
        } else {
          end = toFinite(end);
        }
        step = step === undefined ? (start < end ? 1 : -1) : toFinite(step);
        return baseRange(start, end, step, fromRight);
      };
    }

    /**
     * Creates a function that performs a relational operation on two values.
     *
     * @private
     * @param {Function} operator The function to perform the operation.
     * @returns {Function} Returns the new relational operation function.
     */
    function createRelationalOperation(operator) {
      return function(value, other) {
        if (!(typeof value == 'string' && typeof other == 'string')) {
          value = toNumber(value);
          other = toNumber(other);
        }
        return operator(value, other);
      };
    }

    /**
     * Creates a function that wraps `func` to continue currying.
     *
     * @private
     * @param {Function} func The function to wrap.
     * @param {number} bitmask The bitmask flags. See `createWrap` for more details.
     * @param {Function} wrapFunc The function to create the `func` wrapper.
     * @param {*} placeholder The placeholder value.
     * @param {*} [thisArg] The `this` binding of `func`.
     * @param {Array} [partials] The arguments to prepend to those provided to
     *  the new function.
     * @param {Array} [holders] The `partials` placeholder indexes.
     * @param {Array} [argPos] The argument positions of the new function.
     * @param {number} [ary] The arity cap of `func`.
     * @param {number} [arity] The arity of `func`.
     * @returns {Function} Returns the new wrapped function.
     */
    function createRecurry(func, bitmask, wrapFunc, placeholder, thisArg, partials, holders, argPos, ary, arity) {
      var isCurry = bitmask & WRAP_CURRY_FLAG,
          newHolders = isCurry ? holders : undefined,
          newHoldersRight = isCurry ? undefined : holders,
          newPartials = isCurry ? partials : undefined,
          newPartialsRight = isCurry ? undefined : partials;

      bitmask |= (isCurry ? WRAP_PARTIAL_FLAG : WRAP_PARTIAL_RIGHT_FLAG);
      bitmask &= ~(isCurry ? WRAP_PARTIAL_RIGHT_FLAG : WRAP_PARTIAL_FLAG);

      if (!(bitmask & WRAP_CURRY_BOUND_FLAG)) {
        bitmask &= ~(WRAP_BIND_FLAG | WRAP_BIND_KEY_FLAG);
      }
      var newData = [
        func, bitmask, thisArg, newPartials, newHolders, newPartialsRight,
        newHoldersRight, argPos, ary, arity
      ];

      var result = wrapFunc.apply(undefined, newData);
      if (isLaziable(func)) {
        setData(result, newData);
      }
      result.placeholder = placeholder;
      return setWrapToString(result, func, bitmask);
    }

    /**
     * Creates a function like `_.round`.
     *
     * @private
     * @param {string} methodName The name of the `Math` method to use when rounding.
     * @returns {Function} Returns the new round function.
     */
    function createRound(methodName) {
      var func = Math[methodName];
      return function(number, precision) {
        number = toNumber(number);
        precision = precision == null ? 0 : nativeMin(toInteger(precision), 292);
        if (precision && nativeIsFinite(number)) {
          // Shift with exponential notation to avoid floating-point issues.
          // See [MDN](https://mdn.io/round#Examples) for more details.
          var pair = (toString(number) + 'e').split('e'),
              value = func(pair[0] + 'e' + (+pair[1] + precision));

          pair = (toString(value) + 'e').split('e');
          return +(pair[0] + 'e' + (+pair[1] - precision));
        }
        return func(number);
      };
    }

    /**
     * Creates a set object of `values`.
     *
     * @private
     * @param {Array} values The values to add to the set.
     * @returns {Object} Returns the new set.
     */
    var createSet = !(Set && (1 / setToArray(new Set([,-0]))[1]) == INFINITY) ? noop : function(values) {
      return new Set(values);
    };

    /**
     * Creates a `_.toPairs` or `_.toPairsIn` function.
     *
     * @private
     * @param {Function} keysFunc The function to get the keys of a given object.
     * @returns {Function} Returns the new pairs function.
     */
    function createToPairs(keysFunc) {
      return function(object) {
        var tag = getTag(object);
        if (tag == mapTag) {
          return mapToArray(object);
        }
        if (tag == setTag) {
          return setToPairs(object);
        }
        return baseToPairs(object, keysFunc(object));
      };
    }

    /**
     * Creates a function that either curries or invokes `func` with optional
     * `this` binding and partially applied arguments.
     *
     * @private
     * @param {Function|string} func The function or method name to wrap.
     * @param {number} bitmask The bitmask flags.
     *    1 - `_.bind`
     *    2 - `_.bindKey`
     *    4 - `_.curry` or `_.curryRight` of a bound function
     *    8 - `_.curry`
     *   16 - `_.curryRight`
     *   32 - `_.partial`
     *   64 - `_.partialRight`
     *  128 - `_.rearg`
     *  256 - `_.ary`
     *  512 - `_.flip`
     * @param {*} [thisArg] The `this` binding of `func`.
     * @param {Array} [partials] The arguments to be partially applied.
     * @param {Array} [holders] The `partials` placeholder indexes.
     * @param {Array} [argPos] The argument positions of the new function.
     * @param {number} [ary] The arity cap of `func`.
     * @param {number} [arity] The arity of `func`.
     * @returns {Function} Returns the new wrapped function.
     */
    function createWrap(func, bitmask, thisArg, partials, holders, argPos, ary, arity) {
      var isBindKey = bitmask & WRAP_BIND_KEY_FLAG;
      if (!isBindKey && typeof func != 'function') {
        throw new TypeError(FUNC_ERROR_TEXT);
      }
      var length = partials ? partials.length : 0;
      if (!length) {
        bitmask &= ~(WRAP_PARTIAL_FLAG | WRAP_PARTIAL_RIGHT_FLAG);
        partials = holders = undefined;
      }
      ary = ary === undefined ? ary : nativeMax(toInteger(ary), 0);
      arity = arity === undefined ? arity : toInteger(arity);
      length -= holders ? holders.length : 0;

      if (bitmask & WRAP_PARTIAL_RIGHT_FLAG) {
        var partialsRight = partials,
            holdersRight = holders;

        partials = holders = undefined;
      }
      var data = isBindKey ? undefined : getData(func);

      var newData = [
        func, bitmask, thisArg, partials, holders, partialsRight, holdersRight,
        argPos, ary, arity
      ];

      if (data) {
        mergeData(newData, data);
      }
      func = newData[0];
      bitmask = newData[1];
      thisArg = newData[2];
      partials = newData[3];
      holders = newData[4];
      arity = newData[9] = newData[9] === undefined
        ? (isBindKey ? 0 : func.length)
        : nativeMax(newData[9] - length, 0);

      if (!arity && bitmask & (WRAP_CURRY_FLAG | WRAP_CURRY_RIGHT_FLAG)) {
        bitmask &= ~(WRAP_CURRY_FLAG | WRAP_CURRY_RIGHT_FLAG);
      }
      if (!bitmask || bitmask == WRAP_BIND_FLAG) {
        var result = createBind(func, bitmask, thisArg);
      } else if (bitmask == WRAP_CURRY_FLAG || bitmask == WRAP_CURRY_RIGHT_FLAG) {
        result = createCurry(func, bitmask, arity);
      } else if ((bitmask == WRAP_PARTIAL_FLAG || bitmask == (WRAP_BIND_FLAG | WRAP_PARTIAL_FLAG)) && !holders.length) {
        result = createPartial(func, bitmask, thisArg, partials);
      } else {
        result = createHybrid.apply(undefined, newData);
      }
      var setter = data ? baseSetData : setData;
      return setWrapToString(setter(result, newData), func, bitmask);
    }

    /**
     * Used by `_.defaults` to customize its `_.assignIn` use to assign properties
     * of source objects to the destination object for all destination properties
     * that resolve to `undefined`.
     *
     * @private
     * @param {*} objValue The destination value.
     * @param {*} srcValue The source value.
     * @param {string} key The key of the property to assign.
     * @param {Object} object The parent object of `objValue`.
     * @returns {*} Returns the value to assign.
     */
    function customDefaultsAssignIn(objValue, srcValue, key, object) {
      if (objValue === undefined ||
          (eq(objValue, objectProto[key]) && !hasOwnProperty.call(object, key))) {
        return srcValue;
      }
      return objValue;
    }

    /**
     * Used by `_.defaultsDeep` to customize its `_.merge` use to merge source
     * objects into destination objects that are passed thru.
     *
     * @private
     * @param {*} objValue The destination value.
     * @param {*} srcValue The source value.
     * @param {string} key The key of the property to merge.
     * @param {Object} object The parent object of `objValue`.
     * @param {Object} source The parent object of `srcValue`.
     * @param {Object} [stack] Tracks traversed source values and their merged
     *  counterparts.
     * @returns {*} Returns the value to assign.
     */
    function customDefaultsMerge(objValue, srcValue, key, object, source, stack) {
      if (isObject(objValue) && isObject(srcValue)) {
        // Recursively merge objects and arrays (susceptible to call stack limits).
        stack.set(srcValue, objValue);
        baseMerge(objValue, srcValue, undefined, customDefaultsMerge, stack);
        stack['delete'](srcValue);
      }
      return objValue;
    }

    /**
     * Used by `_.omit` to customize its `_.cloneDeep` use to only clone plain
     * objects.
     *
     * @private
     * @param {*} value The value to inspect.
     * @param {string} key The key of the property to inspect.
     * @returns {*} Returns the uncloned value or `undefined` to defer cloning to `_.cloneDeep`.
     */
    function customOmitClone(value) {
      return isPlainObject(value) ? undefined : value;
    }

    /**
     * A specialized version of `baseIsEqualDeep` for arrays with support for
     * partial deep comparisons.
     *
     * @private
     * @param {Array} array The array to compare.
     * @param {Array} other The other array to compare.
     * @param {number} bitmask The bitmask flags. See `baseIsEqual` for more details.
     * @param {Function} customizer The function to customize comparisons.
     * @param {Function} equalFunc The function to determine equivalents of values.
     * @param {Object} stack Tracks traversed `array` and `other` objects.
     * @returns {boolean} Returns `true` if the arrays are equivalent, else `false`.
     */
    function equalArrays(array, other, bitmask, customizer, equalFunc, stack) {
      var isPartial = bitmask & COMPARE_PARTIAL_FLAG,
          arrLength = array.length,
          othLength = other.length;

      if (arrLength != othLength && !(isPartial && othLength > arrLength)) {
        return false;
      }
      // Check that cyclic values are equal.
      var arrStacked = stack.get(array);
      var othStacked = stack.get(other);
      if (arrStacked && othStacked) {
        return arrStacked == other && othStacked == array;
      }
      var index = -1,
          result = true,
          seen = (bitmask & COMPARE_UNORDERED_FLAG) ? new SetCache : undefined;

      stack.set(array, other);
      stack.set(other, array);

      // Ignore non-index properties.
      while (++index < arrLength) {
        var arrValue = array[index],
            othValue = other[index];

        if (customizer) {
          var compared = isPartial
            ? customizer(othValue, arrValue, index, other, array, stack)
            : customizer(arrValue, othValue, index, array, other, stack);
        }
        if (compared !== undefined) {
          if (compared) {
            continue;
          }
          result = false;
          break;
        }
        // Recursively compare arrays (susceptible to call stack limits).
        if (seen) {
          if (!arraySome(other, function(othValue, othIndex) {
                if (!cacheHas(seen, othIndex) &&
                    (arrValue === othValue || equalFunc(arrValue, othValue, bitmask, customizer, stack))) {
                  return seen.push(othIndex);
                }
              })) {
            result = false;
            break;
          }
        } else if (!(
              arrValue === othValue ||
                equalFunc(arrValue, othValue, bitmask, customizer, stack)
            )) {
          result = false;
          break;
        }
      }
      stack['delete'](array);
      stack['delete'](other);
      return result;
    }

    /**
     * A specialized version of `baseIsEqualDeep` for comparing objects of
     * the same `toStringTag`.
     *
     * **Note:** This function only supports comparing values with tags of
     * `Boolean`, `Date`, `Error`, `Number`, `RegExp`, or `String`.
     *
     * @private
     * @param {Object} object The object to compare.
     * @param {Object} other The other object to compare.
     * @param {string} tag The `toStringTag` of the objects to compare.
     * @param {number} bitmask The bitmask flags. See `baseIsEqual` for more details.
     * @param {Function} customizer The function to customize comparisons.
     * @param {Function} equalFunc The function to determine equivalents of values.
     * @param {Object} stack Tracks traversed `object` and `other` objects.
     * @returns {boolean} Returns `true` if the objects are equivalent, else `false`.
     */
    function equalByTag(object, other, tag, bitmask, customizer, equalFunc, stack) {
      switch (tag) {
        case dataViewTag:
          if ((object.byteLength != other.byteLength) ||
              (object.byteOffset != other.byteOffset)) {
            return false;
          }
          object = object.buffer;
          other = other.buffer;

        case arrayBufferTag:
          if ((object.byteLength != other.byteLength) ||
              !equalFunc(new Uint8Array(object), new Uint8Array(other))) {
            return false;
          }
          return true;

        case boolTag:
        case dateTag:
        case numberTag:
          // Coerce booleans to `1` or `0` and dates to milliseconds.
          // Invalid dates are coerced to `NaN`.
          return eq(+object, +other);

        case errorTag:
          return object.name == other.name && object.message == other.message;

        case regexpTag:
        case stringTag:
          // Coerce regexes to strings and treat strings, primitives and objects,
          // as equal. See http://www.ecma-international.org/ecma-262/7.0/#sec-regexp.prototype.tostring
          // for more details.
          return object == (other + '');

        case mapTag:
          var convert = mapToArray;

        case setTag:
          var isPartial = bitmask & COMPARE_PARTIAL_FLAG;
          convert || (convert = setToArray);

          if (object.size != other.size && !isPartial) {
            return false;
          }
          // Assume cyclic values are equal.
          var stacked = stack.get(object);
          if (stacked) {
            return stacked == other;
          }
          bitmask |= COMPARE_UNORDERED_FLAG;

          // Recursively compare objects (susceptible to call stack limits).
          stack.set(object, other);
          var result = equalArrays(convert(object), convert(other), bitmask, customizer, equalFunc, stack);
          stack['delete'](object);
          return result;

        case symbolTag:
          if (symbolValueOf) {
            return symbolValueOf.call(object) == symbolValueOf.call(other);
          }
      }
      return false;
    }

    /**
     * A specialized version of `baseIsEqualDeep` for objects with support for
     * partial deep comparisons.
     *
     * @private
     * @param {Object} object The object to compare.
     * @param {Object} other The other object to compare.
     * @param {number} bitmask The bitmask flags. See `baseIsEqual` for more details.
     * @param {Function} customizer The function to customize comparisons.
     * @param {Function} equalFunc The function to determine equivalents of values.
     * @param {Object} stack Tracks traversed `object` and `other` objects.
     * @returns {boolean} Returns `true` if the objects are equivalent, else `false`.
     */
    function equalObjects(object, other, bitmask, customizer, equalFunc, stack) {
      var isPartial = bitmask & COMPARE_PARTIAL_FLAG,
          objProps = getAllKeys(object),
          objLength = objProps.length,
          othProps = getAllKeys(other),
          othLength = othProps.length;

      if (objLength != othLength && !isPartial) {
        return false;
      }
      var index = objLength;
      while (index--) {
        var key = objProps[index];
        if (!(isPartial ? key in other : hasOwnProperty.call(other, key))) {
          return false;
        }
      }
      // Check that cyclic values are equal.
      var objStacked = stack.get(object);
      var othStacked = stack.get(other);
      if (objStacked && othStacked) {
        return objStacked == other && othStacked == object;
      }
      var result = true;
      stack.set(object, other);
      stack.set(other, object);

      var skipCtor = isPartial;
      while (++index < objLength) {
        key = objProps[index];
        var objValue = object[key],
            othValue = other[key];

        if (customizer) {
          var compared = isPartial
            ? customizer(othValue, objValue, key, other, object, stack)
            : customizer(objValue, othValue, key, object, other, stack);
        }
        // Recursively compare objects (susceptible to call stack limits).
        if (!(compared === undefined
              ? (objValue === othValue || equalFunc(objValue, othValue, bitmask, customizer, stack))
              : compared
            )) {
          result = false;
          break;
        }
        skipCtor || (skipCtor = key == 'constructor');
      }
      if (result && !skipCtor) {
        var objCtor = object.constructor,
            othCtor = other.constructor;

        // Non `Object` object instances with different constructors are not equal.
        if (objCtor != othCtor &&
            ('constructor' in object && 'constructor' in other) &&
            !(typeof objCtor == 'function' && objCtor instanceof objCtor &&
              typeof othCtor == 'function' && othCtor instanceof othCtor)) {
          result = false;
        }
      }
      stack['delete'](object);
      stack['delete'](other);
      return result;
    }

    /**
     * A specialized version of `baseRest` which flattens the rest array.
     *
     * @private
     * @param {Function} func The function to apply a rest parameter to.
     * @returns {Function} Returns the new function.
     */
    function flatRest(func) {
      return setToString(overRest(func, undefined, flatten), func + '');
    }

    /**
     * Creates an array of own enumerable property names and symbols of `object`.
     *
     * @private
     * @param {Object} object The object to query.
     * @returns {Array} Returns the array of property names and symbols.
     */
    function getAllKeys(object) {
      return baseGetAllKeys(object, keys, getSymbols);
    }

    /**
     * Creates an array of own and inherited enumerable property names and
     * symbols of `object`.
     *
     * @private
     * @param {Object} object The object to query.
     * @returns {Array} Returns the array of property names and symbols.
     */
    function getAllKeysIn(object) {
      return baseGetAllKeys(object, keysIn, getSymbolsIn);
    }

    /**
     * Gets metadata for `func`.
     *
     * @private
     * @param {Function} func The function to query.
     * @returns {*} Returns the metadata for `func`.
     */
    var getData = !metaMap ? noop : function(func) {
      return metaMap.get(func);
    };

    /**
     * Gets the name of `func`.
     *
     * @private
     * @param {Function} func The function to query.
     * @returns {string} Returns the function name.
     */
    function getFuncName(func) {
      var result = (func.name + ''),
          array = realNames[result],
          length = hasOwnProperty.call(realNames, result) ? array.length : 0;

      while (length--) {
        var data = array[length],
            otherFunc = data.func;
        if (otherFunc == null || otherFunc == func) {
          return data.name;
        }
      }
      return result;
    }

    /**
     * Gets the argument placeholder value for `func`.
     *
     * @private
     * @param {Function} func The function to inspect.
     * @returns {*} Returns the placeholder value.
     */
    function getHolder(func) {
      var object = hasOwnProperty.call(lodash, 'placeholder') ? lodash : func;
      return object.placeholder;
    }

    /**
     * Gets the appropriate "iteratee" function. If `_.iteratee` is customized,
     * this function returns the custom method, otherwise it returns `baseIteratee`.
     * If arguments are provided, the chosen function is invoked with them and
     * its result is returned.
     *
     * @private
     * @param {*} [value] The value to convert to an iteratee.
     * @param {number} [arity] The arity of the created iteratee.
     * @returns {Function} Returns the chosen function or its result.
     */
    function getIteratee() {
      var result = lodash.iteratee || iteratee;
      result = result === iteratee ? baseIteratee : result;
      return arguments.length ? result(arguments[0], arguments[1]) : result;
    }

    /**
     * Gets the data for `map`.
     *
     * @private
     * @param {Object} map The map to query.
     * @param {string} key The reference key.
     * @returns {*} Returns the map data.
     */
    function getMapData(map, key) {
      var data = map.__data__;
      return isKeyable(key)
        ? data[typeof key == 'string' ? 'string' : 'hash']
        : data.map;
    }

    /**
     * Gets the property names, values, and compare flags of `object`.
     *
     * @private
     * @param {Object} object The object to query.
     * @returns {Array} Returns the match data of `object`.
     */
    function getMatchData(object) {
      var result = keys(object),
          length = result.length;

      while (length--) {
        var key = result[length],
            value = object[key];

        result[length] = [key, value, isStrictComparable(value)];
      }
      return result;
    }

    /**
     * Gets the native function at `key` of `object`.
     *
     * @private
     * @param {Object} object The object to query.
     * @param {string} key The key of the method to get.
     * @returns {*} Returns the function if it's native, else `undefined`.
     */
    function getNative(object, key) {
      var value = getValue(object, key);
      return baseIsNative(value) ? value : undefined;
    }

    /**
     * A specialized version of `baseGetTag` which ignores `Symbol.toStringTag` values.
     *
     * @private
     * @param {*} value The value to query.
     * @returns {string} Returns the raw `toStringTag`.
     */
    function getRawTag(value) {
      var isOwn = hasOwnProperty.call(value, symToStringTag),
          tag = value[symToStringTag];

      try {
        value[symToStringTag] = undefined;
        var unmasked = true;
      } catch (e) {}

      var result = nativeObjectToString.call(value);
      if (unmasked) {
        if (isOwn) {
          value[symToStringTag] = tag;
        } else {
          delete value[symToStringTag];
        }
      }
      return result;
    }

    /**
     * Creates an array of the own enumerable symbols of `object`.
     *
     * @private
     * @param {Object} object The object to query.
     * @returns {Array} Returns the array of symbols.
     */
    var getSymbols = !nativeGetSymbols ? stubArray : function(object) {
      if (object == null) {
        return [];
      }
      object = Object(object);
      return arrayFilter(nativeGetSymbols(object), function(symbol) {
        return propertyIsEnumerable.call(object, symbol);
      });
    };

    /**
     * Creates an array of the own and inherited enumerable symbols of `object`.
     *
     * @private
     * @param {Object} object The object to query.
     * @returns {Array} Returns the array of symbols.
     */
    var getSymbolsIn = !nativeGetSymbols ? stubArray : function(object) {
      var result = [];
      while (object) {
        arrayPush(result, getSymbols(object));
        object = getPrototype(object);
      }
      return result;
    };

    /**
     * Gets the `toStringTag` of `value`.
     *
     * @private
     * @param {*} value The value to query.
     * @returns {string} Returns the `toStringTag`.
     */
    var getTag = baseGetTag;

    // Fallback for data views, maps, sets, and weak maps in IE 11 and promises in Node.js < 6.
    if ((DataView && getTag(new DataView(new ArrayBuffer(1))) != dataViewTag) ||
        (Map && getTag(new Map) != mapTag) ||
        (Promise && getTag(Promise.resolve()) != promiseTag) ||
        (Set && getTag(new Set) != setTag) ||
        (WeakMap && getTag(new WeakMap) != weakMapTag)) {
      getTag = function(value) {
        var result = baseGetTag(value),
            Ctor = result == objectTag ? value.constructor : undefined,
            ctorString = Ctor ? toSource(Ctor) : '';

        if (ctorString) {
          switch (ctorString) {
            case dataViewCtorString: return dataViewTag;
            case mapCtorString: return mapTag;
            case promiseCtorString: return promiseTag;
            case setCtorString: return setTag;
            case weakMapCtorString: return weakMapTag;
          }
        }
        return result;
      };
    }

    /**
     * Gets the view, applying any `transforms` to the `start` and `end` positions.
     *
     * @private
     * @param {number} start The start of the view.
     * @param {number} end The end of the view.
     * @param {Array} transforms The transformations to apply to the view.
     * @returns {Object} Returns an object containing the `start` and `end`
     *  positions of the view.
     */
    function getView(start, end, transforms) {
      var index = -1,
          length = transforms.length;

      while (++index < length) {
        var data = transforms[index],
            size = data.size;

        switch (data.type) {
          case 'drop':      start += size; break;
          case 'dropRight': end -= size; break;
          case 'take':      end = nativeMin(end, start + size); break;
          case 'takeRight': start = nativeMax(start, end - size); break;
        }
      }
      return { 'start': start, 'end': end };
    }

    /**
     * Extracts wrapper details from the `source` body comment.
     *
     * @private
     * @param {string} source The source to inspect.
     * @returns {Array} Returns the wrapper details.
     */
    function getWrapDetails(source) {
      var match = source.match(reWrapDetails);
      return match ? match[1].split(reSplitDetails) : [];
    }

    /**
     * Checks if `path` exists on `object`.
     *
     * @private
     * @param {Object} object The object to query.
     * @param {Array|string} path The path to check.
     * @param {Function} hasFunc The function to check properties.
     * @returns {boolean} Returns `true` if `path` exists, else `false`.
     */
    function hasPath(object, path, hasFunc) {
      path = castPath(path, object);

      var index = -1,
          length = path.length,
          result = false;

      while (++index < length) {
        var key = toKey(path[index]);
        if (!(result = object != null && hasFunc(object, key))) {
          break;
        }
        object = object[key];
      }
      if (result || ++index != length) {
        return result;
      }
      length = object == null ? 0 : object.length;
      return !!length && isLength(length) && isIndex(key, length) &&
        (isArray(object) || isArguments(object));
    }

    /**
     * Initializes an array clone.
     *
     * @private
     * @param {Array} array The array to clone.
     * @returns {Array} Returns the initialized clone.
     */
    function initCloneArray(array) {
      var length = array.length,
          result = new array.constructor(length);

      // Add properties assigned by `RegExp#exec`.
      if (length && typeof array[0] == 'string' && hasOwnProperty.call(array, 'index')) {
        result.index = array.index;
        result.input = array.input;
      }
      return result;
    }

    /**
     * Initializes an object clone.
     *
     * @private
     * @param {Object} object The object to clone.
     * @returns {Object} Returns the initialized clone.
     */
    function initCloneObject(object) {
      return (typeof object.constructor == 'function' && !isPrototype(object))
        ? baseCreate(getPrototype(object))
        : {};
    }

    /**
     * Initializes an object clone based on its `toStringTag`.
     *
     * **Note:** This function only supports cloning values with tags of
     * `Boolean`, `Date`, `Error`, `Map`, `Number`, `RegExp`, `Set`, or `String`.
     *
     * @private
     * @param {Object} object The object to clone.
     * @param {string} tag The `toStringTag` of the object to clone.
     * @param {boolean} [isDeep] Specify a deep clone.
     * @returns {Object} Returns the initialized clone.
     */
    function initCloneByTag(object, tag, isDeep) {
      var Ctor = object.constructor;
      switch (tag) {
        case arrayBufferTag:
          return cloneArrayBuffer(object);

        case boolTag:
        case dateTag:
          return new Ctor(+object);

        case dataViewTag:
          return cloneDataView(object, isDeep);

        case float32Tag: case float64Tag:
        case int8Tag: case int16Tag: case int32Tag:
        case uint8Tag: case uint8ClampedTag: case uint16Tag: case uint32Tag:
          return cloneTypedArray(object, isDeep);

        case mapTag:
          return new Ctor;

        case numberTag:
        case stringTag:
          return new Ctor(object);

        case regexpTag:
          return cloneRegExp(object);

        case setTag:
          return new Ctor;

        case symbolTag:
          return cloneSymbol(object);
      }
    }

    /**
     * Inserts wrapper `details` in a comment at the top of the `source` body.
     *
     * @private
     * @param {string} source The source to modify.
     * @returns {Array} details The details to insert.
     * @returns {string} Returns the modified source.
     */
    function insertWrapDetails(source, details) {
      var length = details.length;
      if (!length) {
        return source;
      }
      var lastIndex = length - 1;
      details[lastIndex] = (length > 1 ? '& ' : '') + details[lastIndex];
      details = details.join(length > 2 ? ', ' : ' ');
      return source.replace(reWrapComment, '{\n/* [wrapped with ' + details + '] */\n');
    }

    /**
     * Checks if `value` is a flattenable `arguments` object or array.
     *
     * @private
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is flattenable, else `false`.
     */
    function isFlattenable(value) {
      return isArray(value) || isArguments(value) ||
        !!(spreadableSymbol && value && value[spreadableSymbol]);
    }

    /**
     * Checks if `value` is a valid array-like index.
     *
     * @private
     * @param {*} value The value to check.
     * @param {number} [length=MAX_SAFE_INTEGER] The upper bounds of a valid index.
     * @returns {boolean} Returns `true` if `value` is a valid index, else `false`.
     */
    function isIndex(value, length) {
      var type = typeof value;
      length = length == null ? MAX_SAFE_INTEGER : length;

      return !!length &&
        (type == 'number' ||
          (type != 'symbol' && reIsUint.test(value))) &&
            (value > -1 && value % 1 == 0 && value < length);
    }

    /**
     * Checks if the given arguments are from an iteratee call.
     *
     * @private
     * @param {*} value The potential iteratee value argument.
     * @param {*} index The potential iteratee index or key argument.
     * @param {*} object The potential iteratee object argument.
     * @returns {boolean} Returns `true` if the arguments are from an iteratee call,
     *  else `false`.
     */
    function isIterateeCall(value, index, object) {
      if (!isObject(object)) {
        return false;
      }
      var type = typeof index;
      if (type == 'number'
            ? (isArrayLike(object) && isIndex(index, object.length))
            : (type == 'string' && index in object)
          ) {
        return eq(object[index], value);
      }
      return false;
    }

    /**
     * Checks if `value` is a property name and not a property path.
     *
     * @private
     * @param {*} value The value to check.
     * @param {Object} [object] The object to query keys on.
     * @returns {boolean} Returns `true` if `value` is a property name, else `false`.
     */
    function isKey(value, object) {
      if (isArray(value)) {
        return false;
      }
      var type = typeof value;
      if (type == 'number' || type == 'symbol' || type == 'boolean' ||
          value == null || isSymbol(value)) {
        return true;
      }
      return reIsPlainProp.test(value) || !reIsDeepProp.test(value) ||
        (object != null && value in Object(object));
    }

    /**
     * Checks if `value` is suitable for use as unique object key.
     *
     * @private
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is suitable, else `false`.
     */
    function isKeyable(value) {
      var type = typeof value;
      return (type == 'string' || type == 'number' || type == 'symbol' || type == 'boolean')
        ? (value !== '__proto__')
        : (value === null);
    }

    /**
     * Checks if `func` has a lazy counterpart.
     *
     * @private
     * @param {Function} func The function to check.
     * @returns {boolean} Returns `true` if `func` has a lazy counterpart,
     *  else `false`.
     */
    function isLaziable(func) {
      var funcName = getFuncName(func),
          other = lodash[funcName];

      if (typeof other != 'function' || !(funcName in LazyWrapper.prototype)) {
        return false;
      }
      if (func === other) {
        return true;
      }
      var data = getData(other);
      return !!data && func === data[0];
    }

    /**
     * Checks if `func` has its source masked.
     *
     * @private
     * @param {Function} func The function to check.
     * @returns {boolean} Returns `true` if `func` is masked, else `false`.
     */
    function isMasked(func) {
      return !!maskSrcKey && (maskSrcKey in func);
    }

    /**
     * Checks if `func` is capable of being masked.
     *
     * @private
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `func` is maskable, else `false`.
     */
    var isMaskable = coreJsData ? isFunction : stubFalse;

    /**
     * Checks if `value` is likely a prototype object.
     *
     * @private
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is a prototype, else `false`.
     */
    function isPrototype(value) {
      var Ctor = value && value.constructor,
          proto = (typeof Ctor == 'function' && Ctor.prototype) || objectProto;

      return value === proto;
    }

    /**
     * Checks if `value` is suitable for strict equality comparisons, i.e. `===`.
     *
     * @private
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` if suitable for strict
     *  equality comparisons, else `false`.
     */
    function isStrictComparable(value) {
      return value === value && !isObject(value);
    }

    /**
     * A specialized version of `matchesProperty` for source values suitable
     * for strict equality comparisons, i.e. `===`.
     *
     * @private
     * @param {string} key The key of the property to get.
     * @param {*} srcValue The value to match.
     * @returns {Function} Returns the new spec function.
     */
    function matchesStrictComparable(key, srcValue) {
      return function(object) {
        if (object == null) {
          return false;
        }
        return object[key] === srcValue &&
          (srcValue !== undefined || (key in Object(object)));
      };
    }

    /**
     * A specialized version of `_.memoize` which clears the memoized function's
     * cache when it exceeds `MAX_MEMOIZE_SIZE`.
     *
     * @private
     * @param {Function} func The function to have its output memoized.
     * @returns {Function} Returns the new memoized function.
     */
    function memoizeCapped(func) {
      var result = memoize(func, function(key) {
        if (cache.size === MAX_MEMOIZE_SIZE) {
          cache.clear();
        }
        return key;
      });

      var cache = result.cache;
      return result;
    }

    /**
     * Merges the function metadata of `source` into `data`.
     *
     * Merging metadata reduces the number of wrappers used to invoke a function.
     * This is possible because methods like `_.bind`, `_.curry`, and `_.partial`
     * may be applied regardless of execution order. Methods like `_.ary` and
     * `_.rearg` modify function arguments, making the order in which they are
     * executed important, preventing the merging of metadata. However, we make
     * an exception for a safe combined case where curried functions have `_.ary`
     * and or `_.rearg` applied.
     *
     * @private
     * @param {Array} data The destination metadata.
     * @param {Array} source The source metadata.
     * @returns {Array} Returns `data`.
     */
    function mergeData(data, source) {
      var bitmask = data[1],
          srcBitmask = source[1],
          newBitmask = bitmask | srcBitmask,
          isCommon = newBitmask < (WRAP_BIND_FLAG | WRAP_BIND_KEY_FLAG | WRAP_ARY_FLAG);

      var isCombo =
        ((srcBitmask == WRAP_ARY_FLAG) && (bitmask == WRAP_CURRY_FLAG)) ||
        ((srcBitmask == WRAP_ARY_FLAG) && (bitmask == WRAP_REARG_FLAG) && (data[7].length <= source[8])) ||
        ((srcBitmask == (WRAP_ARY_FLAG | WRAP_REARG_FLAG)) && (source[7].length <= source[8]) && (bitmask == WRAP_CURRY_FLAG));

      // Exit early if metadata can't be merged.
      if (!(isCommon || isCombo)) {
        return data;
      }
      // Use source `thisArg` if available.
      if (srcBitmask & WRAP_BIND_FLAG) {
        data[2] = source[2];
        // Set when currying a bound function.
        newBitmask |= bitmask & WRAP_BIND_FLAG ? 0 : WRAP_CURRY_BOUND_FLAG;
      }
      // Compose partial arguments.
      var value = source[3];
      if (value) {
        var partials = data[3];
        data[3] = partials ? composeArgs(partials, value, source[4]) : value;
        data[4] = partials ? replaceHolders(data[3], PLACEHOLDER) : source[4];
      }
      // Compose partial right arguments.
      value = source[5];
      if (value) {
        partials = data[5];
        data[5] = partials ? composeArgsRight(partials, value, source[6]) : value;
        data[6] = partials ? replaceHolders(data[5], PLACEHOLDER) : source[6];
      }
      // Use source `argPos` if available.
      value = source[7];
      if (value) {
        data[7] = value;
      }
      // Use source `ary` if it's smaller.
      if (srcBitmask & WRAP_ARY_FLAG) {
        data[8] = data[8] == null ? source[8] : nativeMin(data[8], source[8]);
      }
      // Use source `arity` if one is not provided.
      if (data[9] == null) {
        data[9] = source[9];
      }
      // Use source `func` and merge bitmasks.
      data[0] = source[0];
      data[1] = newBitmask;

      return data;
    }

    /**
     * This function is like
     * [`Object.keys`](http://ecma-international.org/ecma-262/7.0/#sec-object.keys)
     * except that it includes inherited enumerable properties.
     *
     * @private
     * @param {Object} object The object to query.
     * @returns {Array} Returns the array of property names.
     */
    function nativeKeysIn(object) {
      var result = [];
      if (object != null) {
        for (var key in Object(object)) {
          result.push(key);
        }
      }
      return result;
    }

    /**
     * Converts `value` to a string using `Object.prototype.toString`.
     *
     * @private
     * @param {*} value The value to convert.
     * @returns {string} Returns the converted string.
     */
    function objectToString(value) {
      return nativeObjectToString.call(value);
    }

    /**
     * A specialized version of `baseRest` which transforms the rest array.
     *
     * @private
     * @param {Function} func The function to apply a rest parameter to.
     * @param {number} [start=func.length-1] The start position of the rest parameter.
     * @param {Function} transform The rest array transform.
     * @returns {Function} Returns the new function.
     */
    function overRest(func, start, transform) {
      start = nativeMax(start === undefined ? (func.length - 1) : start, 0);
      return function() {
        var args = arguments,
            index = -1,
            length = nativeMax(args.length - start, 0),
            array = Array(length);

        while (++index < length) {
          array[index] = args[start + index];
        }
        index = -1;
        var otherArgs = Array(start + 1);
        while (++index < start) {
          otherArgs[index] = args[index];
        }
        otherArgs[start] = transform(array);
        return apply(func, this, otherArgs);
      };
    }

    /**
     * Gets the parent value at `path` of `object`.
     *
     * @private
     * @param {Object} object The object to query.
     * @param {Array} path The path to get the parent value of.
     * @returns {*} Returns the parent value.
     */
    function parent(object, path) {
      return path.length < 2 ? object : baseGet(object, baseSlice(path, 0, -1));
    }

    /**
     * Reorder `array` according to the specified indexes where the element at
     * the first index is assigned as the first element, the element at
     * the second index is assigned as the second element, and so on.
     *
     * @private
     * @param {Array} array The array to reorder.
     * @param {Array} indexes The arranged array indexes.
     * @returns {Array} Returns `array`.
     */
    function reorder(array, indexes) {
      var arrLength = array.length,
          length = nativeMin(indexes.length, arrLength),
          oldArray = copyArray(array);

      while (length--) {
        var index = indexes[length];
        array[length] = isIndex(index, arrLength) ? oldArray[index] : undefined;
      }
      return array;
    }

    /**
     * Gets the value at `key`, unless `key` is "__proto__" or "constructor".
     *
     * @private
     * @param {Object} object The object to query.
     * @param {string} key The key of the property to get.
     * @returns {*} Returns the property value.
     */
    function safeGet(object, key) {
      if (key === 'constructor' && typeof object[key] === 'function') {
        return;
      }

      if (key == '__proto__') {
        return;
      }

      return object[key];
    }

    /**
     * Sets metadata for `func`.
     *
     * **Note:** If this function becomes hot, i.e. is invoked a lot in a short
     * period of time, it will trip its breaker and transition to an identity
     * function to avoid garbage collection pauses in V8. See
     * [V8 issue 2070](https://bugs.chromium.org/p/v8/issues/detail?id=2070)
     * for more details.
     *
     * @private
     * @param {Function} func The function to associate metadata with.
     * @param {*} data The metadata.
     * @returns {Function} Returns `func`.
     */
    var setData = shortOut(baseSetData);

    /**
     * A simple wrapper around the global [`setTimeout`](https://mdn.io/setTimeout).
     *
     * @private
     * @param {Function} func The function to delay.
     * @param {number} wait The number of milliseconds to delay invocation.
     * @returns {number|Object} Returns the timer id or timeout object.
     */
    var setTimeout = ctxSetTimeout || function(func, wait) {
      return root.setTimeout(func, wait);
    };

    /**
     * Sets the `toString` method of `func` to return `string`.
     *
     * @private
     * @param {Function} func The function to modify.
     * @param {Function} string The `toString` result.
     * @returns {Function} Returns `func`.
     */
    var setToString = shortOut(baseSetToString);

    /**
     * Sets the `toString` method of `wrapper` to mimic the source of `reference`
     * with wrapper details in a comment at the top of the source body.
     *
     * @private
     * @param {Function} wrapper The function to modify.
     * @param {Function} reference The reference function.
     * @param {number} bitmask The bitmask flags. See `createWrap` for more details.
     * @returns {Function} Returns `wrapper`.
     */
    function setWrapToString(wrapper, reference, bitmask) {
      var source = (reference + '');
      return setToString(wrapper, insertWrapDetails(source, updateWrapDetails(getWrapDetails(source), bitmask)));
    }

    /**
     * Creates a function that'll short out and invoke `identity` instead
     * of `func` when it's called `HOT_COUNT` or more times in `HOT_SPAN`
     * milliseconds.
     *
     * @private
     * @param {Function} func The function to restrict.
     * @returns {Function} Returns the new shortable function.
     */
    function shortOut(func) {
      var count = 0,
          lastCalled = 0;

      return function() {
        var stamp = nativeNow(),
            remaining = HOT_SPAN - (stamp - lastCalled);

        lastCalled = stamp;
        if (remaining > 0) {
          if (++count >= HOT_COUNT) {
            return arguments[0];
          }
        } else {
          count = 0;
        }
        return func.apply(undefined, arguments);
      };
    }

    /**
     * A specialized version of `_.shuffle` which mutates and sets the size of `array`.
     *
     * @private
     * @param {Array} array The array to shuffle.
     * @param {number} [size=array.length] The size of `array`.
     * @returns {Array} Returns `array`.
     */
    function shuffleSelf(array, size) {
      var index = -1,
          length = array.length,
          lastIndex = length - 1;

      size = size === undefined ? length : size;
      while (++index < size) {
        var rand = baseRandom(index, lastIndex),
            value = array[rand];

        array[rand] = array[index];
        array[index] = value;
      }
      array.length = size;
      return array;
    }

    /**
     * Converts `string` to a property path array.
     *
     * @private
     * @param {string} string The string to convert.
     * @returns {Array} Returns the property path array.
     */
    var stringToPath = memoizeCapped(function(string) {
      var result = [];
      if (string.charCodeAt(0) === 46 /* . */) {
        result.push('');
      }
      string.replace(rePropName, function(match, number, quote, subString) {
        result.push(quote ? subString.replace(reEscapeChar, '$1') : (number || match));
      });
      return result;
    });

    /**
     * Converts `value` to a string key if it's not a string or symbol.
     *
     * @private
     * @param {*} value The value to inspect.
     * @returns {string|symbol} Returns the key.
     */
    function toKey(value) {
      if (typeof value == 'string' || isSymbol(value)) {
        return value;
      }
      var result = (value + '');
      return (result == '0' && (1 / value) == -INFINITY) ? '-0' : result;
    }

    /**
     * Converts `func` to its source code.
     *
     * @private
     * @param {Function} func The function to convert.
     * @returns {string} Returns the source code.
     */
    function toSource(func) {
      if (func != null) {
        try {
          return funcToString.call(func);
        } catch (e) {}
        try {
          return (func + '');
        } catch (e) {}
      }
      return '';
    }

    /**
     * Updates wrapper `details` based on `bitmask` flags.
     *
     * @private
     * @returns {Array} details The details to modify.
     * @param {number} bitmask The bitmask flags. See `createWrap` for more details.
     * @returns {Array} Returns `details`.
     */
    function updateWrapDetails(details, bitmask) {
      arrayEach(wrapFlags, function(pair) {
        var value = '_.' + pair[0];
        if ((bitmask & pair[1]) && !arrayIncludes(details, value)) {
          details.push(value);
        }
      });
      return details.sort();
    }

    /**
     * Creates a clone of `wrapper`.
     *
     * @private
     * @param {Object} wrapper The wrapper to clone.
     * @returns {Object} Returns the cloned wrapper.
     */
    function wrapperClone(wrapper) {
      if (wrapper instanceof LazyWrapper) {
        return wrapper.clone();
      }
      var result = new LodashWrapper(wrapper.__wrapped__, wrapper.__chain__);
      result.__actions__ = copyArray(wrapper.__actions__);
      result.__index__  = wrapper.__index__;
      result.__values__ = wrapper.__values__;
      return result;
    }

    /*------------------------------------------------------------------------*/

    /**
     * Creates an array of elements split into groups the length of `size`.
     * If `array` can't be split evenly, the final chunk will be the remaining
     * elements.
     *
     * @static
     * @memberOf _
     * @since 3.0.0
     * @category Array
     * @param {Array} array The array to process.
     * @param {number} [size=1] The length of each chunk
     * @param- {Object} [guard] Enables use as an iteratee for methods like `_.map`.
     * @returns {Array} Returns the new array of chunks.
     * @example
     *
     * _.chunk(['a', 'b', 'c', 'd'], 2);
     * // => [['a', 'b'], ['c', 'd']]
     *
     * _.chunk(['a', 'b', 'c', 'd'], 3);
     * // => [['a', 'b', 'c'], ['d']]
     */
    function chunk(array, size, guard) {
      if ((guard ? isIterateeCall(array, size, guard) : size === undefined)) {
        size = 1;
      } else {
        size = nativeMax(toInteger(size), 0);
      }
      var length = array == null ? 0 : array.length;
      if (!length || size < 1) {
        return [];
      }
      var index = 0,
          resIndex = 0,
          result = Array(nativeCeil(length / size));

      while (index < length) {
        result[resIndex++] = baseSlice(array, index, (index += size));
      }
      return result;
    }

    /**
     * Creates an array with all falsey values removed. The values `false`, `null`,
     * `0`, `""`, `undefined`, and `NaN` are falsey.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Array
     * @param {Array} array The array to compact.
     * @returns {Array} Returns the new array of filtered values.
     * @example
     *
     * _.compact([0, 1, false, 2, '', 3]);
     * // => [1, 2, 3]
     */
    function compact(array) {
      var index = -1,
          length = array == null ? 0 : array.length,
          resIndex = 0,
          result = [];

      while (++index < length) {
        var value = array[index];
        if (value) {
          result[resIndex++] = value;
        }
      }
      return result;
    }

    /**
     * Creates a new array concatenating `array` with any additional arrays
     * and/or values.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Array
     * @param {Array} array The array to concatenate.
     * @param {...*} [values] The values to concatenate.
     * @returns {Array} Returns the new concatenated array.
     * @example
     *
     * var array = [1];
     * var other = _.concat(array, 2, [3], [[4]]);
     *
     * console.log(other);
     * // => [1, 2, 3, [4]]
     *
     * console.log(array);
     * // => [1]
     */
    function concat() {
      var length = arguments.length;
      if (!length) {
        return [];
      }
      var args = Array(length - 1),
          array = arguments[0],
          index = length;

      while (index--) {
        args[index - 1] = arguments[index];
      }
      return arrayPush(isArray(array) ? copyArray(array) : [array], baseFlatten(args, 1));
    }

    /**
     * Creates an array of `array` values not included in the other given arrays
     * using [`SameValueZero`](http://ecma-international.org/ecma-262/7.0/#sec-samevaluezero)
     * for equality comparisons. The order and references of result values are
     * determined by the first array.
     *
     * **Note:** Unlike `_.pullAll`, this method returns a new array.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Array
     * @param {Array} array The array to inspect.
     * @param {...Array} [values] The values to exclude.
     * @returns {Array} Returns the new array of filtered values.
     * @see _.without, _.xor
     * @example
     *
     * _.difference([2, 1], [2, 3]);
     * // => [1]
     */
    var difference = baseRest(function(array, values) {
      return isArrayLikeObject(array)
        ? baseDifference(array, baseFlatten(values, 1, isArrayLikeObject, true))
        : [];
    });

    /**
     * This method is like `_.difference` except that it accepts `iteratee` which
     * is invoked for each element of `array` and `values` to generate the criterion
     * by which they're compared. The order and references of result values are
     * determined by the first array. The iteratee is invoked with one argument:
     * (value).
     *
     * **Note:** Unlike `_.pullAllBy`, this method returns a new array.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Array
     * @param {Array} array The array to inspect.
     * @param {...Array} [values] The values to exclude.
     * @param {Function} [iteratee=_.identity] The iteratee invoked per element.
     * @returns {Array} Returns the new array of filtered values.
     * @example
     *
     * _.differenceBy([2.1, 1.2], [2.3, 3.4], Math.floor);
     * // => [1.2]
     *
     * // The `_.property` iteratee shorthand.
     * _.differenceBy([{ 'x': 2 }, { 'x': 1 }], [{ 'x': 1 }], 'x');
     * // => [{ 'x': 2 }]
     */
    var differenceBy = baseRest(function(array, values) {
      var iteratee = last(values);
      if (isArrayLikeObject(iteratee)) {
        iteratee = undefined;
      }
      return isArrayLikeObject(array)
        ? baseDifference(array, baseFlatten(values, 1, isArrayLikeObject, true), getIteratee(iteratee, 2))
        : [];
    });

    /**
     * This method is like `_.difference` except that it accepts `comparator`
     * which is invoked to compare elements of `array` to `values`. The order and
     * references of result values are determined by the first array. The comparator
     * is invoked with two arguments: (arrVal, othVal).
     *
     * **Note:** Unlike `_.pullAllWith`, this method returns a new array.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Array
     * @param {Array} array The array to inspect.
     * @param {...Array} [values] The values to exclude.
     * @param {Function} [comparator] The comparator invoked per element.
     * @returns {Array} Returns the new array of filtered values.
     * @example
     *
     * var objects = [{ 'x': 1, 'y': 2 }, { 'x': 2, 'y': 1 }];
     *
     * _.differenceWith(objects, [{ 'x': 1, 'y': 2 }], _.isEqual);
     * // => [{ 'x': 2, 'y': 1 }]
     */
    var differenceWith = baseRest(function(array, values) {
      var comparator = last(values);
      if (isArrayLikeObject(comparator)) {
        comparator = undefined;
      }
      return isArrayLikeObject(array)
        ? baseDifference(array, baseFlatten(values, 1, isArrayLikeObject, true), undefined, comparator)
        : [];
    });

    /**
     * Creates a slice of `array` with `n` elements dropped from the beginning.
     *
     * @static
     * @memberOf _
     * @since 0.5.0
     * @category Array
     * @param {Array} array The array to query.
     * @param {number} [n=1] The number of elements to drop.
     * @param- {Object} [guard] Enables use as an iteratee for methods like `_.map`.
     * @returns {Array} Returns the slice of `array`.
     * @example
     *
     * _.drop([1, 2, 3]);
     * // => [2, 3]
     *
     * _.drop([1, 2, 3], 2);
     * // => [3]
     *
     * _.drop([1, 2, 3], 5);
     * // => []
     *
     * _.drop([1, 2, 3], 0);
     * // => [1, 2, 3]
     */
    function drop(array, n, guard) {
      var length = array == null ? 0 : array.length;
      if (!length) {
        return [];
      }
      n = (guard || n === undefined) ? 1 : toInteger(n);
      return baseSlice(array, n < 0 ? 0 : n, length);
    }

    /**
     * Creates a slice of `array` with `n` elements dropped from the end.
     *
     * @static
     * @memberOf _
     * @since 3.0.0
     * @category Array
     * @param {Array} array The array to query.
     * @param {number} [n=1] The number of elements to drop.
     * @param- {Object} [guard] Enables use as an iteratee for methods like `_.map`.
     * @returns {Array} Returns the slice of `array`.
     * @example
     *
     * _.dropRight([1, 2, 3]);
     * // => [1, 2]
     *
     * _.dropRight([1, 2, 3], 2);
     * // => [1]
     *
     * _.dropRight([1, 2, 3], 5);
     * // => []
     *
     * _.dropRight([1, 2, 3], 0);
     * // => [1, 2, 3]
     */
    function dropRight(array, n, guard) {
      var length = array == null ? 0 : array.length;
      if (!length) {
        return [];
      }
      n = (guard || n === undefined) ? 1 : toInteger(n);
      n = length - n;
      return baseSlice(array, 0, n < 0 ? 0 : n);
    }

    /**
     * Creates a slice of `array` excluding elements dropped from the end.
     * Elements are dropped until `predicate` returns falsey. The predicate is
     * invoked with three arguments: (value, index, array).
     *
     * @static
     * @memberOf _
     * @since 3.0.0
     * @category Array
     * @param {Array} array The array to query.
     * @param {Function} [predicate=_.identity] The function invoked per iteration.
     * @returns {Array} Returns the slice of `array`.
     * @example
     *
     * var users = [
     *   { 'user': 'barney',  'active': true },
     *   { 'user': 'fred',    'active': false },
     *   { 'user': 'pebbles', 'active': false }
     * ];
     *
     * _.dropRightWhile(users, function(o) { return !o.active; });
     * // => objects for ['barney']
     *
     * // The `_.matches` iteratee shorthand.
     * _.dropRightWhile(users, { 'user': 'pebbles', 'active': false });
     * // => objects for ['barney', 'fred']
     *
     * // The `_.matchesProperty` iteratee shorthand.
     * _.dropRightWhile(users, ['active', false]);
     * // => objects for ['barney']
     *
     * // The `_.property` iteratee shorthand.
     * _.dropRightWhile(users, 'active');
     * // => objects for ['barney', 'fred', 'pebbles']
     */
    function dropRightWhile(array, predicate) {
      return (array && array.length)
        ? baseWhile(array, getIteratee(predicate, 3), true, true)
        : [];
    }

    /**
     * Creates a slice of `array` excluding elements dropped from the beginning.
     * Elements are dropped until `predicate` returns falsey. The predicate is
     * invoked with three arguments: (value, index, array).
     *
     * @static
     * @memberOf _
     * @since 3.0.0
     * @category Array
     * @param {Array} array The array to query.
     * @param {Function} [predicate=_.identity] The function invoked per iteration.
     * @returns {Array} Returns the slice of `array`.
     * @example
     *
     * var users = [
     *   { 'user': 'barney',  'active': false },
     *   { 'user': 'fred',    'active': false },
     *   { 'user': 'pebbles', 'active': true }
     * ];
     *
     * _.dropWhile(users, function(o) { return !o.active; });
     * // => objects for ['pebbles']
     *
     * // The `_.matches` iteratee shorthand.
     * _.dropWhile(users, { 'user': 'barney', 'active': false });
     * // => objects for ['fred', 'pebbles']
     *
     * // The `_.matchesProperty` iteratee shorthand.
     * _.dropWhile(users, ['active', false]);
     * // => objects for ['pebbles']
     *
     * // The `_.property` iteratee shorthand.
     * _.dropWhile(users, 'active');
     * // => objects for ['barney', 'fred', 'pebbles']
     */
    function dropWhile(array, predicate) {
      return (array && array.length)
        ? baseWhile(array, getIteratee(predicate, 3), true)
        : [];
    }

    /**
     * Fills elements of `array` with `value` from `start` up to, but not
     * including, `end`.
     *
     * **Note:** This method mutates `array`.
     *
     * @static
     * @memberOf _
     * @since 3.2.0
     * @category Array
     * @param {Array} array The array to fill.
     * @param {*} value The value to fill `array` with.
     * @param {number} [start=0] The start position.
     * @param {number} [end=array.length] The end position.
     * @returns {Array} Returns `array`.
     * @example
     *
     * var array = [1, 2, 3];
     *
     * _.fill(array, 'a');
     * console.log(array);
     * // => ['a', 'a', 'a']
     *
     * _.fill(Array(3), 2);
     * // => [2, 2, 2]
     *
     * _.fill([4, 6, 8, 10], '*', 1, 3);
     * // => [4, '*', '*', 10]
     */
    function fill(array, value, start, end) {
      var length = array == null ? 0 : array.length;
      if (!length) {
        return [];
      }
      if (start && typeof start != 'number' && isIterateeCall(array, value, start)) {
        start = 0;
        end = length;
      }
      return baseFill(array, value, start, end);
    }

    /**
     * This method is like `_.find` except that it returns the index of the first
     * element `predicate` returns truthy for instead of the element itself.
     *
     * @static
     * @memberOf _
     * @since 1.1.0
     * @category Array
     * @param {Array} array The array to inspect.
     * @param {Function} [predicate=_.identity] The function invoked per iteration.
     * @param {number} [fromIndex=0] The index to search from.
     * @returns {number} Returns the index of the found element, else `-1`.
     * @example
     *
     * var users = [
     *   { 'user': 'barney',  'active': false },
     *   { 'user': 'fred',    'active': false },
     *   { 'user': 'pebbles', 'active': true }
     * ];
     *
     * _.findIndex(users, function(o) { return o.user == 'barney'; });
     * // => 0
     *
     * // The `_.matches` iteratee shorthand.
     * _.findIndex(users, { 'user': 'fred', 'active': false });
     * // => 1
     *
     * // The `_.matchesProperty` iteratee shorthand.
     * _.findIndex(users, ['active', false]);
     * // => 0
     *
     * // The `_.property` iteratee shorthand.
     * _.findIndex(users, 'active');
     * // => 2
     */
    function findIndex(array, predicate, fromIndex) {
      var length = array == null ? 0 : array.length;
      if (!length) {
        return -1;
      }
      var index = fromIndex == null ? 0 : toInteger(fromIndex);
      if (index < 0) {
        index = nativeMax(length + index, 0);
      }
      return baseFindIndex(array, getIteratee(predicate, 3), index);
    }

    /**
     * This method is like `_.findIndex` except that it iterates over elements
     * of `collection` from right to left.
     *
     * @static
     * @memberOf _
     * @since 2.0.0
     * @category Array
     * @param {Array} array The array to inspect.
     * @param {Function} [predicate=_.identity] The function invoked per iteration.
     * @param {number} [fromIndex=array.length-1] The index to search from.
     * @returns {number} Returns the index of the found element, else `-1`.
     * @example
     *
     * var users = [
     *   { 'user': 'barney',  'active': true },
     *   { 'user': 'fred',    'active': false },
     *   { 'user': 'pebbles', 'active': false }
     * ];
     *
     * _.findLastIndex(users, function(o) { return o.user == 'pebbles'; });
     * // => 2
     *
     * // The `_.matches` iteratee shorthand.
     * _.findLastIndex(users, { 'user': 'barney', 'active': true });
     * // => 0
     *
     * // The `_.matchesProperty` iteratee shorthand.
     * _.findLastIndex(users, ['active', false]);
     * // => 2
     *
     * // The `_.property` iteratee shorthand.
     * _.findLastIndex(users, 'active');
     * // => 0
     */
    function findLastIndex(array, predicate, fromIndex) {
      var length = array == null ? 0 : array.length;
      if (!length) {
        return -1;
      }
      var index = length - 1;
      if (fromIndex !== undefined) {
        index = toInteger(fromIndex);
        index = fromIndex < 0
          ? nativeMax(length + index, 0)
          : nativeMin(index, length - 1);
      }
      return baseFindIndex(array, getIteratee(predicate, 3), index, true);
    }

    /**
     * Flattens `array` a single level deep.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Array
     * @param {Array} array The array to flatten.
     * @returns {Array} Returns the new flattened array.
     * @example
     *
     * _.flatten([1, [2, [3, [4]], 5]]);
     * // => [1, 2, [3, [4]], 5]
     */
    function flatten(array) {
      var length = array == null ? 0 : array.length;
      return length ? baseFlatten(array, 1) : [];
    }

    /**
     * Recursively flattens `array`.
     *
     * @static
     * @memberOf _
     * @since 3.0.0
     * @category Array
     * @param {Array} array The array to flatten.
     * @returns {Array} Returns the new flattened array.
     * @example
     *
     * _.flattenDeep([1, [2, [3, [4]], 5]]);
     * // => [1, 2, 3, 4, 5]
     */
    function flattenDeep(array) {
      var length = array == null ? 0 : array.length;
      return length ? baseFlatten(array, INFINITY) : [];
    }

    /**
     * Recursively flatten `array` up to `depth` times.
     *
     * @static
     * @memberOf _
     * @since 4.4.0
     * @category Array
     * @param {Array} array The array to flatten.
     * @param {number} [depth=1] The maximum recursion depth.
     * @returns {Array} Returns the new flattened array.
     * @example
     *
     * var array = [1, [2, [3, [4]], 5]];
     *
     * _.flattenDepth(array, 1);
     * // => [1, 2, [3, [4]], 5]
     *
     * _.flattenDepth(array, 2);
     * // => [1, 2, 3, [4], 5]
     */
    function flattenDepth(array, depth) {
      var length = array == null ? 0 : array.length;
      if (!length) {
        return [];
      }
      depth = depth === undefined ? 1 : toInteger(depth);
      return baseFlatten(array, depth);
    }

    /**
     * The inverse of `_.toPairs`; this method returns an object composed
     * from key-value `pairs`.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Array
     * @param {Array} pairs The key-value pairs.
     * @returns {Object} Returns the new object.
     * @example
     *
     * _.fromPairs([['a', 1], ['b', 2]]);
     * // => { 'a': 1, 'b': 2 }
     */
    function fromPairs(pairs) {
      var index = -1,
          length = pairs == null ? 0 : pairs.length,
          result = {};

      while (++index < length) {
        var pair = pairs[index];
        result[pair[0]] = pair[1];
      }
      return result;
    }

    /**
     * Gets the first element of `array`.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @alias first
     * @category Array
     * @param {Array} array The array to query.
     * @returns {*} Returns the first element of `array`.
     * @example
     *
     * _.head([1, 2, 3]);
     * // => 1
     *
     * _.head([]);
     * // => undefined
     */
    function head(array) {
      return (array && array.length) ? array[0] : undefined;
    }

    /**
     * Gets the index at which the first occurrence of `value` is found in `array`
     * using [`SameValueZero`](http://ecma-international.org/ecma-262/7.0/#sec-samevaluezero)
     * for equality comparisons. If `fromIndex` is negative, it's used as the
     * offset from the end of `array`.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Array
     * @param {Array} array The array to inspect.
     * @param {*} value The value to search for.
     * @param {number} [fromIndex=0] The index to search from.
     * @returns {number} Returns the index of the matched value, else `-1`.
     * @example
     *
     * _.indexOf([1, 2, 1, 2], 2);
     * // => 1
     *
     * // Search from the `fromIndex`.
     * _.indexOf([1, 2, 1, 2], 2, 2);
     * // => 3
     */
    function indexOf(array, value, fromIndex) {
      var length = array == null ? 0 : array.length;
      if (!length) {
        return -1;
      }
      var index = fromIndex == null ? 0 : toInteger(fromIndex);
      if (index < 0) {
        index = nativeMax(length + index, 0);
      }
      return baseIndexOf(array, value, index);
    }

    /**
     * Gets all but the last element of `array`.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Array
     * @param {Array} array The array to query.
     * @returns {Array} Returns the slice of `array`.
     * @example
     *
     * _.initial([1, 2, 3]);
     * // => [1, 2]
     */
    function initial(array) {
      var length = array == null ? 0 : array.length;
      return length ? baseSlice(array, 0, -1) : [];
    }

    /**
     * Creates an array of unique values that are included in all given arrays
     * using [`SameValueZero`](http://ecma-international.org/ecma-262/7.0/#sec-samevaluezero)
     * for equality comparisons. The order and references of result values are
     * determined by the first array.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Array
     * @param {...Array} [arrays] The arrays to inspect.
     * @returns {Array} Returns the new array of intersecting values.
     * @example
     *
     * _.intersection([2, 1], [2, 3]);
     * // => [2]
     */
    var intersection = baseRest(function(arrays) {
      var mapped = arrayMap(arrays, castArrayLikeObject);
      return (mapped.length && mapped[0] === arrays[0])
        ? baseIntersection(mapped)
        : [];
    });

    /**
     * This method is like `_.intersection` except that it accepts `iteratee`
     * which is invoked for each element of each `arrays` to generate the criterion
     * by which they're compared. The order and references of result values are
     * determined by the first array. The iteratee is invoked with one argument:
     * (value).
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Array
     * @param {...Array} [arrays] The arrays to inspect.
     * @param {Function} [iteratee=_.identity] The iteratee invoked per element.
     * @returns {Array} Returns the new array of intersecting values.
     * @example
     *
     * _.intersectionBy([2.1, 1.2], [2.3, 3.4], Math.floor);
     * // => [2.1]
     *
     * // The `_.property` iteratee shorthand.
     * _.intersectionBy([{ 'x': 1 }], [{ 'x': 2 }, { 'x': 1 }], 'x');
     * // => [{ 'x': 1 }]
     */
    var intersectionBy = baseRest(function(arrays) {
      var iteratee = last(arrays),
          mapped = arrayMap(arrays, castArrayLikeObject);

      if (iteratee === last(mapped)) {
        iteratee = undefined;
      } else {
        mapped.pop();
      }
      return (mapped.length && mapped[0] === arrays[0])
        ? baseIntersection(mapped, getIteratee(iteratee, 2))
        : [];
    });

    /**
     * This method is like `_.intersection` except that it accepts `comparator`
     * which is invoked to compare elements of `arrays`. The order and references
     * of result values are determined by the first array. The comparator is
     * invoked with two arguments: (arrVal, othVal).
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Array
     * @param {...Array} [arrays] The arrays to inspect.
     * @param {Function} [comparator] The comparator invoked per element.
     * @returns {Array} Returns the new array of intersecting values.
     * @example
     *
     * var objects = [{ 'x': 1, 'y': 2 }, { 'x': 2, 'y': 1 }];
     * var others = [{ 'x': 1, 'y': 1 }, { 'x': 1, 'y': 2 }];
     *
     * _.intersectionWith(objects, others, _.isEqual);
     * // => [{ 'x': 1, 'y': 2 }]
     */
    var intersectionWith = baseRest(function(arrays) {
      var comparator = last(arrays),
          mapped = arrayMap(arrays, castArrayLikeObject);

      comparator = typeof comparator == 'function' ? comparator : undefined;
      if (comparator) {
        mapped.pop();
      }
      return (mapped.length && mapped[0] === arrays[0])
        ? baseIntersection(mapped, undefined, comparator)
        : [];
    });

    /**
     * Converts all elements in `array` into a string separated by `separator`.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Array
     * @param {Array} array The array to convert.
     * @param {string} [separator=','] The element separator.
     * @returns {string} Returns the joined string.
     * @example
     *
     * _.join(['a', 'b', 'c'], '~');
     * // => 'a~b~c'
     */
    function join(array, separator) {
      return array == null ? '' : nativeJoin.call(array, separator);
    }

    /**
     * Gets the last element of `array`.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Array
     * @param {Array} array The array to query.
     * @returns {*} Returns the last element of `array`.
     * @example
     *
     * _.last([1, 2, 3]);
     * // => 3
     */
    function last(array) {
      var length = array == null ? 0 : array.length;
      return length ? array[length - 1] : undefined;
    }

    /**
     * This method is like `_.indexOf` except that it iterates over elements of
     * `array` from right to left.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Array
     * @param {Array} array The array to inspect.
     * @param {*} value The value to search for.
     * @param {number} [fromIndex=array.length-1] The index to search from.
     * @returns {number} Returns the index of the matched value, else `-1`.
     * @example
     *
     * _.lastIndexOf([1, 2, 1, 2], 2);
     * // => 3
     *
     * // Search from the `fromIndex`.
     * _.lastIndexOf([1, 2, 1, 2], 2, 2);
     * // => 1
     */
    function lastIndexOf(array, value, fromIndex) {
      var length = array == null ? 0 : array.length;
      if (!length) {
        return -1;
      }
      var index = length;
      if (fromIndex !== undefined) {
        index = toInteger(fromIndex);
        index = index < 0 ? nativeMax(length + index, 0) : nativeMin(index, length - 1);
      }
      return value === value
        ? strictLastIndexOf(array, value, index)
        : baseFindIndex(array, baseIsNaN, index, true);
    }

    /**
     * Gets the element at index `n` of `array`. If `n` is negative, the nth
     * element from the end is returned.
     *
     * @static
     * @memberOf _
     * @since 4.11.0
     * @category Array
     * @param {Array} array The array to query.
     * @param {number} [n=0] The index of the element to return.
     * @returns {*} Returns the nth element of `array`.
     * @example
     *
     * var array = ['a', 'b', 'c', 'd'];
     *
     * _.nth(array, 1);
     * // => 'b'
     *
     * _.nth(array, -2);
     * // => 'c';
     */
    function nth(array, n) {
      return (array && array.length) ? baseNth(array, toInteger(n)) : undefined;
    }

    /**
     * Removes all given values from `array` using
     * [`SameValueZero`](http://ecma-international.org/ecma-262/7.0/#sec-samevaluezero)
     * for equality comparisons.
     *
     * **Note:** Unlike `_.without`, this method mutates `array`. Use `_.remove`
     * to remove elements from an array by predicate.
     *
     * @static
     * @memberOf _
     * @since 2.0.0
     * @category Array
     * @param {Array} array The array to modify.
     * @param {...*} [values] The values to remove.
     * @returns {Array} Returns `array`.
     * @example
     *
     * var array = ['a', 'b', 'c', 'a', 'b', 'c'];
     *
     * _.pull(array, 'a', 'c');
     * console.log(array);
     * // => ['b', 'b']
     */
    var pull = baseRest(pullAll);

    /**
     * This method is like `_.pull` except that it accepts an array of values to remove.
     *
     * **Note:** Unlike `_.difference`, this method mutates `array`.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Array
     * @param {Array} array The array to modify.
     * @param {Array} values The values to remove.
     * @returns {Array} Returns `array`.
     * @example
     *
     * var array = ['a', 'b', 'c', 'a', 'b', 'c'];
     *
     * _.pullAll(array, ['a', 'c']);
     * console.log(array);
     * // => ['b', 'b']
     */
    function pullAll(array, values) {
      return (array && array.length && values && values.length)
        ? basePullAll(array, values)
        : array;
    }

    /**
     * This method is like `_.pullAll` except that it accepts `iteratee` which is
     * invoked for each element of `array` and `values` to generate the criterion
     * by which they're compared. The iteratee is invoked with one argument: (value).
     *
     * **Note:** Unlike `_.differenceBy`, this method mutates `array`.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Array
     * @param {Array} array The array to modify.
     * @param {Array} values The values to remove.
     * @param {Function} [iteratee=_.identity] The iteratee invoked per element.
     * @returns {Array} Returns `array`.
     * @example
     *
     * var array = [{ 'x': 1 }, { 'x': 2 }, { 'x': 3 }, { 'x': 1 }];
     *
     * _.pullAllBy(array, [{ 'x': 1 }, { 'x': 3 }], 'x');
     * console.log(array);
     * // => [{ 'x': 2 }]
     */
    function pullAllBy(array, values, iteratee) {
      return (array && array.length && values && values.length)
        ? basePullAll(array, values, getIteratee(iteratee, 2))
        : array;
    }

    /**
     * This method is like `_.pullAll` except that it accepts `comparator` which
     * is invoked to compare elements of `array` to `values`. The comparator is
     * invoked with two arguments: (arrVal, othVal).
     *
     * **Note:** Unlike `_.differenceWith`, this method mutates `array`.
     *
     * @static
     * @memberOf _
     * @since 4.6.0
     * @category Array
     * @param {Array} array The array to modify.
     * @param {Array} values The values to remove.
     * @param {Function} [comparator] The comparator invoked per element.
     * @returns {Array} Returns `array`.
     * @example
     *
     * var array = [{ 'x': 1, 'y': 2 }, { 'x': 3, 'y': 4 }, { 'x': 5, 'y': 6 }];
     *
     * _.pullAllWith(array, [{ 'x': 3, 'y': 4 }], _.isEqual);
     * console.log(array);
     * // => [{ 'x': 1, 'y': 2 }, { 'x': 5, 'y': 6 }]
     */
    function pullAllWith(array, values, comparator) {
      return (array && array.length && values && values.length)
        ? basePullAll(array, values, undefined, comparator)
        : array;
    }

    /**
     * Removes elements from `array` corresponding to `indexes` and returns an
     * array of removed elements.
     *
     * **Note:** Unlike `_.at`, this method mutates `array`.
     *
     * @static
     * @memberOf _
     * @since 3.0.0
     * @category Array
     * @param {Array} array The array to modify.
     * @param {...(number|number[])} [indexes] The indexes of elements to remove.
     * @returns {Array} Returns the new array of removed elements.
     * @example
     *
     * var array = ['a', 'b', 'c', 'd'];
     * var pulled = _.pullAt(array, [1, 3]);
     *
     * console.log(array);
     * // => ['a', 'c']
     *
     * console.log(pulled);
     * // => ['b', 'd']
     */
    var pullAt = flatRest(function(array, indexes) {
      var length = array == null ? 0 : array.length,
          result = baseAt(array, indexes);

      basePullAt(array, arrayMap(indexes, function(index) {
        return isIndex(index, length) ? +index : index;
      }).sort(compareAscending));

      return result;
    });

    /**
     * Removes all elements from `array` that `predicate` returns truthy for
     * and returns an array of the removed elements. The predicate is invoked
     * with three arguments: (value, index, array).
     *
     * **Note:** Unlike `_.filter`, this method mutates `array`. Use `_.pull`
     * to pull elements from an array by value.
     *
     * @static
     * @memberOf _
     * @since 2.0.0
     * @category Array
     * @param {Array} array The array to modify.
     * @param {Function} [predicate=_.identity] The function invoked per iteration.
     * @returns {Array} Returns the new array of removed elements.
     * @example
     *
     * var array = [1, 2, 3, 4];
     * var evens = _.remove(array, function(n) {
     *   return n % 2 == 0;
     * });
     *
     * console.log(array);
     * // => [1, 3]
     *
     * console.log(evens);
     * // => [2, 4]
     */
    function remove(array, predicate) {
      var result = [];
      if (!(array && array.length)) {
        return result;
      }
      var index = -1,
          indexes = [],
          length = array.length;

      predicate = getIteratee(predicate, 3);
      while (++index < length) {
        var value = array[index];
        if (predicate(value, index, array)) {
          result.push(value);
          indexes.push(index);
        }
      }
      basePullAt(array, indexes);
      return result;
    }

    /**
     * Reverses `array` so that the first element becomes the last, the second
     * element becomes the second to last, and so on.
     *
     * **Note:** This method mutates `array` and is based on
     * [`Array#reverse`](https://mdn.io/Array/reverse).
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Array
     * @param {Array} array The array to modify.
     * @returns {Array} Returns `array`.
     * @example
     *
     * var array = [1, 2, 3];
     *
     * _.reverse(array);
     * // => [3, 2, 1]
     *
     * console.log(array);
     * // => [3, 2, 1]
     */
    function reverse(array) {
      return array == null ? array : nativeReverse.call(array);
    }

    /**
     * Creates a slice of `array` from `start` up to, but not including, `end`.
     *
     * **Note:** This method is used instead of
     * [`Array#slice`](https://mdn.io/Array/slice) to ensure dense arrays are
     * returned.
     *
     * @static
     * @memberOf _
     * @since 3.0.0
     * @category Array
     * @param {Array} array The array to slice.
     * @param {number} [start=0] The start position.
     * @param {number} [end=array.length] The end position.
     * @returns {Array} Returns the slice of `array`.
     */
    function slice(array, start, end) {
      var length = array == null ? 0 : array.length;
      if (!length) {
        return [];
      }
      if (end && typeof end != 'number' && isIterateeCall(array, start, end)) {
        start = 0;
        end = length;
      }
      else {
        start = start == null ? 0 : toInteger(start);
        end = end === undefined ? length : toInteger(end);
      }
      return baseSlice(array, start, end);
    }

    /**
     * Uses a binary search to determine the lowest index at which `value`
     * should be inserted into `array` in order to maintain its sort order.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Array
     * @param {Array} array The sorted array to inspect.
     * @param {*} value The value to evaluate.
     * @returns {number} Returns the index at which `value` should be inserted
     *  into `array`.
     * @example
     *
     * _.sortedIndex([30, 50], 40);
     * // => 1
     */
    function sortedIndex(array, value) {
      return baseSortedIndex(array, value);
    }

    /**
     * This method is like `_.sortedIndex` except that it accepts `iteratee`
     * which is invoked for `value` and each element of `array` to compute their
     * sort ranking. The iteratee is invoked with one argument: (value).
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Array
     * @param {Array} array The sorted array to inspect.
     * @param {*} value The value to evaluate.
     * @param {Function} [iteratee=_.identity] The iteratee invoked per element.
     * @returns {number} Returns the index at which `value` should be inserted
     *  into `array`.
     * @example
     *
     * var objects = [{ 'x': 4 }, { 'x': 5 }];
     *
     * _.sortedIndexBy(objects, { 'x': 4 }, function(o) { return o.x; });
     * // => 0
     *
     * // The `_.property` iteratee shorthand.
     * _.sortedIndexBy(objects, { 'x': 4 }, 'x');
     * // => 0
     */
    function sortedIndexBy(array, value, iteratee) {
      return baseSortedIndexBy(array, value, getIteratee(iteratee, 2));
    }

    /**
     * This method is like `_.indexOf` except that it performs a binary
     * search on a sorted `array`.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Array
     * @param {Array} array The array to inspect.
     * @param {*} value The value to search for.
     * @returns {number} Returns the index of the matched value, else `-1`.
     * @example
     *
     * _.sortedIndexOf([4, 5, 5, 5, 6], 5);
     * // => 1
     */
    function sortedIndexOf(array, value) {
      var length = array == null ? 0 : array.length;
      if (length) {
        var index = baseSortedIndex(array, value);
        if (index < length && eq(array[index], value)) {
          return index;
        }
      }
      return -1;
    }

    /**
     * This method is like `_.sortedIndex` except that it returns the highest
     * index at which `value` should be inserted into `array` in order to
     * maintain its sort order.
     *
     * @static
     * @memberOf _
     * @since 3.0.0
     * @category Array
     * @param {Array} array The sorted array to inspect.
     * @param {*} value The value to evaluate.
     * @returns {number} Returns the index at which `value` should be inserted
     *  into `array`.
     * @example
     *
     * _.sortedLastIndex([4, 5, 5, 5, 6], 5);
     * // => 4
     */
    function sortedLastIndex(array, value) {
      return baseSortedIndex(array, value, true);
    }

    /**
     * This method is like `_.sortedLastIndex` except that it accepts `iteratee`
     * which is invoked for `value` and each element of `array` to compute their
     * sort ranking. The iteratee is invoked with one argument: (value).
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Array
     * @param {Array} array The sorted array to inspect.
     * @param {*} value The value to evaluate.
     * @param {Function} [iteratee=_.identity] The iteratee invoked per element.
     * @returns {number} Returns the index at which `value` should be inserted
     *  into `array`.
     * @example
     *
     * var objects = [{ 'x': 4 }, { 'x': 5 }];
     *
     * _.sortedLastIndexBy(objects, { 'x': 4 }, function(o) { return o.x; });
     * // => 1
     *
     * // The `_.property` iteratee shorthand.
     * _.sortedLastIndexBy(objects, { 'x': 4 }, 'x');
     * // => 1
     */
    function sortedLastIndexBy(array, value, iteratee) {
      return baseSortedIndexBy(array, value, getIteratee(iteratee, 2), true);
    }

    /**
     * This method is like `_.lastIndexOf` except that it performs a binary
     * search on a sorted `array`.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Array
     * @param {Array} array The array to inspect.
     * @param {*} value The value to search for.
     * @returns {number} Returns the index of the matched value, else `-1`.
     * @example
     *
     * _.sortedLastIndexOf([4, 5, 5, 5, 6], 5);
     * // => 3
     */
    function sortedLastIndexOf(array, value) {
      var length = array == null ? 0 : array.length;
      if (length) {
        var index = baseSortedIndex(array, value, true) - 1;
        if (eq(array[index], value)) {
          return index;
        }
      }
      return -1;
    }

    /**
     * This method is like `_.uniq` except that it's designed and optimized
     * for sorted arrays.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Array
     * @param {Array} array The array to inspect.
     * @returns {Array} Returns the new duplicate free array.
     * @example
     *
     * _.sortedUniq([1, 1, 2]);
     * // => [1, 2]
     */
    function sortedUniq(array) {
      return (array && array.length)
        ? baseSortedUniq(array)
        : [];
    }

    /**
     * This method is like `_.uniqBy` except that it's designed and optimized
     * for sorted arrays.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Array
     * @param {Array} array The array to inspect.
     * @param {Function} [iteratee] The iteratee invoked per element.
     * @returns {Array} Returns the new duplicate free array.
     * @example
     *
     * _.sortedUniqBy([1.1, 1.2, 2.3, 2.4], Math.floor);
     * // => [1.1, 2.3]
     */
    function sortedUniqBy(array, iteratee) {
      return (array && array.length)
        ? baseSortedUniq(array, getIteratee(iteratee, 2))
        : [];
    }

    /**
     * Gets all but the first element of `array`.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Array
     * @param {Array} array The array to query.
     * @returns {Array} Returns the slice of `array`.
     * @example
     *
     * _.tail([1, 2, 3]);
     * // => [2, 3]
     */
    function tail(array) {
      var length = array == null ? 0 : array.length;
      return length ? baseSlice(array, 1, length) : [];
    }

    /**
     * Creates a slice of `array` with `n` elements taken from the beginning.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Array
     * @param {Array} array The array to query.
     * @param {number} [n=1] The number of elements to take.
     * @param- {Object} [guard] Enables use as an iteratee for methods like `_.map`.
     * @returns {Array} Returns the slice of `array`.
     * @example
     *
     * _.take([1, 2, 3]);
     * // => [1]
     *
     * _.take([1, 2, 3], 2);
     * // => [1, 2]
     *
     * _.take([1, 2, 3], 5);
     * // => [1, 2, 3]
     *
     * _.take([1, 2, 3], 0);
     * // => []
     */
    function take(array, n, guard) {
      if (!(array && array.length)) {
        return [];
      }
      n = (guard || n === undefined) ? 1 : toInteger(n);
      return baseSlice(array, 0, n < 0 ? 0 : n);
    }

    /**
     * Creates a slice of `array` with `n` elements taken from the end.
     *
     * @static
     * @memberOf _
     * @since 3.0.0
     * @category Array
     * @param {Array} array The array to query.
     * @param {number} [n=1] The number of elements to take.
     * @param- {Object} [guard] Enables use as an iteratee for methods like `_.map`.
     * @returns {Array} Returns the slice of `array`.
     * @example
     *
     * _.takeRight([1, 2, 3]);
     * // => [3]
     *
     * _.takeRight([1, 2, 3], 2);
     * // => [2, 3]
     *
     * _.takeRight([1, 2, 3], 5);
     * // => [1, 2, 3]
     *
     * _.takeRight([1, 2, 3], 0);
     * // => []
     */
    function takeRight(array, n, guard) {
      var length = array == null ? 0 : array.length;
      if (!length) {
        return [];
      }
      n = (guard || n === undefined) ? 1 : toInteger(n);
      n = length - n;
      return baseSlice(array, n < 0 ? 0 : n, length);
    }

    /**
     * Creates a slice of `array` with elements taken from the end. Elements are
     * taken until `predicate` returns falsey. The predicate is invoked with
     * three arguments: (value, index, array).
     *
     * @static
     * @memberOf _
     * @since 3.0.0
     * @category Array
     * @param {Array} array The array to query.
     * @param {Function} [predicate=_.identity] The function invoked per iteration.
     * @returns {Array} Returns the slice of `array`.
     * @example
     *
     * var users = [
     *   { 'user': 'barney',  'active': true },
     *   { 'user': 'fred',    'active': false },
     *   { 'user': 'pebbles', 'active': false }
     * ];
     *
     * _.takeRightWhile(users, function(o) { return !o.active; });
     * // => objects for ['fred', 'pebbles']
     *
     * // The `_.matches` iteratee shorthand.
     * _.takeRightWhile(users, { 'user': 'pebbles', 'active': false });
     * // => objects for ['pebbles']
     *
     * // The `_.matchesProperty` iteratee shorthand.
     * _.takeRightWhile(users, ['active', false]);
     * // => objects for ['fred', 'pebbles']
     *
     * // The `_.property` iteratee shorthand.
     * _.takeRightWhile(users, 'active');
     * // => []
     */
    function takeRightWhile(array, predicate) {
      return (array && array.length)
        ? baseWhile(array, getIteratee(predicate, 3), false, true)
        : [];
    }

    /**
     * Creates a slice of `array` with elements taken from the beginning. Elements
     * are taken until `predicate` returns falsey. The predicate is invoked with
     * three arguments: (value, index, array).
     *
     * @static
     * @memberOf _
     * @since 3.0.0
     * @category Array
     * @param {Array} array The array to query.
     * @param {Function} [predicate=_.identity] The function invoked per iteration.
     * @returns {Array} Returns the slice of `array`.
     * @example
     *
     * var users = [
     *   { 'user': 'barney',  'active': false },
     *   { 'user': 'fred',    'active': false },
     *   { 'user': 'pebbles', 'active': true }
     * ];
     *
     * _.takeWhile(users, function(o) { return !o.active; });
     * // => objects for ['barney', 'fred']
     *
     * // The `_.matches` iteratee shorthand.
     * _.takeWhile(users, { 'user': 'barney', 'active': false });
     * // => objects for ['barney']
     *
     * // The `_.matchesProperty` iteratee shorthand.
     * _.takeWhile(users, ['active', false]);
     * // => objects for ['barney', 'fred']
     *
     * // The `_.property` iteratee shorthand.
     * _.takeWhile(users, 'active');
     * // => []
     */
    function takeWhile(array, predicate) {
      return (array && array.length)
        ? baseWhile(array, getIteratee(predicate, 3))
        : [];
    }

    /**
     * Creates an array of unique values, in order, from all given arrays using
     * [`SameValueZero`](http://ecma-international.org/ecma-262/7.0/#sec-samevaluezero)
     * for equality comparisons.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Array
     * @param {...Array} [arrays] The arrays to inspect.
     * @returns {Array} Returns the new array of combined values.
     * @example
     *
     * _.union([2], [1, 2]);
     * // => [2, 1]
     */
    var union = baseRest(function(arrays) {
      return baseUniq(baseFlatten(arrays, 1, isArrayLikeObject, true));
    });

    /**
     * This method is like `_.union` except that it accepts `iteratee` which is
     * invoked for each element of each `arrays` to generate the criterion by
     * which uniqueness is computed. Result values are chosen from the first
     * array in which the value occurs. The iteratee is invoked with one argument:
     * (value).
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Array
     * @param {...Array} [arrays] The arrays to inspect.
     * @param {Function} [iteratee=_.identity] The iteratee invoked per element.
     * @returns {Array} Returns the new array of combined values.
     * @example
     *
     * _.unionBy([2.1], [1.2, 2.3], Math.floor);
     * // => [2.1, 1.2]
     *
     * // The `_.property` iteratee shorthand.
     * _.unionBy([{ 'x': 1 }], [{ 'x': 2 }, { 'x': 1 }], 'x');
     * // => [{ 'x': 1 }, { 'x': 2 }]
     */
    var unionBy = baseRest(function(arrays) {
      var iteratee = last(arrays);
      if (isArrayLikeObject(iteratee)) {
        iteratee = undefined;
      }
      return baseUniq(baseFlatten(arrays, 1, isArrayLikeObject, true), getIteratee(iteratee, 2));
    });

    /**
     * This method is like `_.union` except that it accepts `comparator` which
     * is invoked to compare elements of `arrays`. Result values are chosen from
     * the first array in which the value occurs. The comparator is invoked
     * with two arguments: (arrVal, othVal).
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Array
     * @param {...Array} [arrays] The arrays to inspect.
     * @param {Function} [comparator] The comparator invoked per element.
     * @returns {Array} Returns the new array of combined values.
     * @example
     *
     * var objects = [{ 'x': 1, 'y': 2 }, { 'x': 2, 'y': 1 }];
     * var others = [{ 'x': 1, 'y': 1 }, { 'x': 1, 'y': 2 }];
     *
     * _.unionWith(objects, others, _.isEqual);
     * // => [{ 'x': 1, 'y': 2 }, { 'x': 2, 'y': 1 }, { 'x': 1, 'y': 1 }]
     */
    var unionWith = baseRest(function(arrays) {
      var comparator = last(arrays);
      comparator = typeof comparator == 'function' ? comparator : undefined;
      return baseUniq(baseFlatten(arrays, 1, isArrayLikeObject, true), undefined, comparator);
    });

    /**
     * Creates a duplicate-free version of an array, using
     * [`SameValueZero`](http://ecma-international.org/ecma-262/7.0/#sec-samevaluezero)
     * for equality comparisons, in which only the first occurrence of each element
     * is kept. The order of result values is determined by the order they occur
     * in the array.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Array
     * @param {Array} array The array to inspect.
     * @returns {Array} Returns the new duplicate free array.
     * @example
     *
     * _.uniq([2, 1, 2]);
     * // => [2, 1]
     */
    function uniq(array) {
      return (array && array.length) ? baseUniq(array) : [];
    }

    /**
     * This method is like `_.uniq` except that it accepts `iteratee` which is
     * invoked for each element in `array` to generate the criterion by which
     * uniqueness is computed. The order of result values is determined by the
     * order they occur in the array. The iteratee is invoked with one argument:
     * (value).
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Array
     * @param {Array} array The array to inspect.
     * @param {Function} [iteratee=_.identity] The iteratee invoked per element.
     * @returns {Array} Returns the new duplicate free array.
     * @example
     *
     * _.uniqBy([2.1, 1.2, 2.3], Math.floor);
     * // => [2.1, 1.2]
     *
     * // The `_.property` iteratee shorthand.
     * _.uniqBy([{ 'x': 1 }, { 'x': 2 }, { 'x': 1 }], 'x');
     * // => [{ 'x': 1 }, { 'x': 2 }]
     */
    function uniqBy(array, iteratee) {
      return (array && array.length) ? baseUniq(array, getIteratee(iteratee, 2)) : [];
    }

    /**
     * This method is like `_.uniq` except that it accepts `comparator` which
     * is invoked to compare elements of `array`. The order of result values is
     * determined by the order they occur in the array.The comparator is invoked
     * with two arguments: (arrVal, othVal).
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Array
     * @param {Array} array The array to inspect.
     * @param {Function} [comparator] The comparator invoked per element.
     * @returns {Array} Returns the new duplicate free array.
     * @example
     *
     * var objects = [{ 'x': 1, 'y': 2 }, { 'x': 2, 'y': 1 }, { 'x': 1, 'y': 2 }];
     *
     * _.uniqWith(objects, _.isEqual);
     * // => [{ 'x': 1, 'y': 2 }, { 'x': 2, 'y': 1 }]
     */
    function uniqWith(array, comparator) {
      comparator = typeof comparator == 'function' ? comparator : undefined;
      return (array && array.length) ? baseUniq(array, undefined, comparator) : [];
    }

    /**
     * This method is like `_.zip` except that it accepts an array of grouped
     * elements and creates an array regrouping the elements to their pre-zip
     * configuration.
     *
     * @static
     * @memberOf _
     * @since 1.2.0
     * @category Array
     * @param {Array} array The array of grouped elements to process.
     * @returns {Array} Returns the new array of regrouped elements.
     * @example
     *
     * var zipped = _.zip(['a', 'b'], [1, 2], [true, false]);
     * // => [['a', 1, true], ['b', 2, false]]
     *
     * _.unzip(zipped);
     * // => [['a', 'b'], [1, 2], [true, false]]
     */
    function unzip(array) {
      if (!(array && array.length)) {
        return [];
      }
      var length = 0;
      array = arrayFilter(array, function(group) {
        if (isArrayLikeObject(group)) {
          length = nativeMax(group.length, length);
          return true;
        }
      });
      return baseTimes(length, function(index) {
        return arrayMap(array, baseProperty(index));
      });
    }

    /**
     * This method is like `_.unzip` except that it accepts `iteratee` to specify
     * how regrouped values should be combined. The iteratee is invoked with the
     * elements of each group: (...group).
     *
     * @static
     * @memberOf _
     * @since 3.8.0
     * @category Array
     * @param {Array} array The array of grouped elements to process.
     * @param {Function} [iteratee=_.identity] The function to combine
     *  regrouped values.
     * @returns {Array} Returns the new array of regrouped elements.
     * @example
     *
     * var zipped = _.zip([1, 2], [10, 20], [100, 200]);
     * // => [[1, 10, 100], [2, 20, 200]]
     *
     * _.unzipWith(zipped, _.add);
     * // => [3, 30, 300]
     */
    function unzipWith(array, iteratee) {
      if (!(array && array.length)) {
        return [];
      }
      var result = unzip(array);
      if (iteratee == null) {
        return result;
      }
      return arrayMap(result, function(group) {
        return apply(iteratee, undefined, group);
      });
    }

    /**
     * Creates an array excluding all given values using
     * [`SameValueZero`](http://ecma-international.org/ecma-262/7.0/#sec-samevaluezero)
     * for equality comparisons.
     *
     * **Note:** Unlike `_.pull`, this method returns a new array.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Array
     * @param {Array} array The array to inspect.
     * @param {...*} [values] The values to exclude.
     * @returns {Array} Returns the new array of filtered values.
     * @see _.difference, _.xor
     * @example
     *
     * _.without([2, 1, 2, 3], 1, 2);
     * // => [3]
     */
    var without = baseRest(function(array, values) {
      return isArrayLikeObject(array)
        ? baseDifference(array, values)
        : [];
    });

    /**
     * Creates an array of unique values that is the
     * [symmetric difference](https://en.wikipedia.org/wiki/Symmetric_difference)
     * of the given arrays. The order of result values is determined by the order
     * they occur in the arrays.
     *
     * @static
     * @memberOf _
     * @since 2.4.0
     * @category Array
     * @param {...Array} [arrays] The arrays to inspect.
     * @returns {Array} Returns the new array of filtered values.
     * @see _.difference, _.without
     * @example
     *
     * _.xor([2, 1], [2, 3]);
     * // => [1, 3]
     */
    var xor = baseRest(function(arrays) {
      return baseXor(arrayFilter(arrays, isArrayLikeObject));
    });

    /**
     * This method is like `_.xor` except that it accepts `iteratee` which is
     * invoked for each element of each `arrays` to generate the criterion by
     * which by which they're compared. The order of result values is determined
     * by the order they occur in the arrays. The iteratee is invoked with one
     * argument: (value).
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Array
     * @param {...Array} [arrays] The arrays to inspect.
     * @param {Function} [iteratee=_.identity] The iteratee invoked per element.
     * @returns {Array} Returns the new array of filtered values.
     * @example
     *
     * _.xorBy([2.1, 1.2], [2.3, 3.4], Math.floor);
     * // => [1.2, 3.4]
     *
     * // The `_.property` iteratee shorthand.
     * _.xorBy([{ 'x': 1 }], [{ 'x': 2 }, { 'x': 1 }], 'x');
     * // => [{ 'x': 2 }]
     */
    var xorBy = baseRest(function(arrays) {
      var iteratee = last(arrays);
      if (isArrayLikeObject(iteratee)) {
        iteratee = undefined;
      }
      return baseXor(arrayFilter(arrays, isArrayLikeObject), getIteratee(iteratee, 2));
    });

    /**
     * This method is like `_.xor` except that it accepts `comparator` which is
     * invoked to compare elements of `arrays`. The order of result values is
     * determined by the order they occur in the arrays. The comparator is invoked
     * with two arguments: (arrVal, othVal).
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Array
     * @param {...Array} [arrays] The arrays to inspect.
     * @param {Function} [comparator] The comparator invoked per element.
     * @returns {Array} Returns the new array of filtered values.
     * @example
     *
     * var objects = [{ 'x': 1, 'y': 2 }, { 'x': 2, 'y': 1 }];
     * var others = [{ 'x': 1, 'y': 1 }, { 'x': 1, 'y': 2 }];
     *
     * _.xorWith(objects, others, _.isEqual);
     * // => [{ 'x': 2, 'y': 1 }, { 'x': 1, 'y': 1 }]
     */
    var xorWith = baseRest(function(arrays) {
      var comparator = last(arrays);
      comparator = typeof comparator == 'function' ? comparator : undefined;
      return baseXor(arrayFilter(arrays, isArrayLikeObject), undefined, comparator);
    });

    /**
     * Creates an array of grouped elements, the first of which contains the
     * first elements of the given arrays, the second of which contains the
     * second elements of the given arrays, and so on.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Array
     * @param {...Array} [arrays] The arrays to process.
     * @returns {Array} Returns the new array of grouped elements.
     * @example
     *
     * _.zip(['a', 'b'], [1, 2], [true, false]);
     * // => [['a', 1, true], ['b', 2, false]]
     */
    var zip = baseRest(unzip);

    /**
     * This method is like `_.fromPairs` except that it accepts two arrays,
     * one of property identifiers and one of corresponding values.
     *
     * @static
     * @memberOf _
     * @since 0.4.0
     * @category Array
     * @param {Array} [props=[]] The property identifiers.
     * @param {Array} [values=[]] The property values.
     * @returns {Object} Returns the new object.
     * @example
     *
     * _.zipObject(['a', 'b'], [1, 2]);
     * // => { 'a': 1, 'b': 2 }
     */
    function zipObject(props, values) {
      return baseZipObject(props || [], values || [], assignValue);
    }

    /**
     * This method is like `_.zipObject` except that it supports property paths.
     *
     * @static
     * @memberOf _
     * @since 4.1.0
     * @category Array
     * @param {Array} [props=[]] The property identifiers.
     * @param {Array} [values=[]] The property values.
     * @returns {Object} Returns the new object.
     * @example
     *
     * _.zipObjectDeep(['a.b[0].c', 'a.b[1].d'], [1, 2]);
     * // => { 'a': { 'b': [{ 'c': 1 }, { 'd': 2 }] } }
     */
    function zipObjectDeep(props, values) {
      return baseZipObject(props || [], values || [], baseSet);
    }

    /**
     * This method is like `_.zip` except that it accepts `iteratee` to specify
     * how grouped values should be combined. The iteratee is invoked with the
     * elements of each group: (...group).
     *
     * @static
     * @memberOf _
     * @since 3.8.0
     * @category Array
     * @param {...Array} [arrays] The arrays to process.
     * @param {Function} [iteratee=_.identity] The function to combine
     *  grouped values.
     * @returns {Array} Returns the new array of grouped elements.
     * @example
     *
     * _.zipWith([1, 2], [10, 20], [100, 200], function(a, b, c) {
     *   return a + b + c;
     * });
     * // => [111, 222]
     */
    var zipWith = baseRest(function(arrays) {
      var length = arrays.length,
          iteratee = length > 1 ? arrays[length - 1] : undefined;

      iteratee = typeof iteratee == 'function' ? (arrays.pop(), iteratee) : undefined;
      return unzipWith(arrays, iteratee);
    });

    /*------------------------------------------------------------------------*/

    /**
     * Creates a `lodash` wrapper instance that wraps `value` with explicit method
     * chain sequences enabled. The result of such sequences must be unwrapped
     * with `_#value`.
     *
     * @static
     * @memberOf _
     * @since 1.3.0
     * @category Seq
     * @param {*} value The value to wrap.
     * @returns {Object} Returns the new `lodash` wrapper instance.
     * @example
     *
     * var users = [
     *   { 'user': 'barney',  'age': 36 },
     *   { 'user': 'fred',    'age': 40 },
     *   { 'user': 'pebbles', 'age': 1 }
     * ];
     *
     * var youngest = _
     *   .chain(users)
     *   .sortBy('age')
     *   .map(function(o) {
     *     return o.user + ' is ' + o.age;
     *   })
     *   .head()
     *   .value();
     * // => 'pebbles is 1'
     */
    function chain(value) {
      var result = lodash(value);
      result.__chain__ = true;
      return result;
    }

    /**
     * This method invokes `interceptor` and returns `value`. The interceptor
     * is invoked with one argument; (value). The purpose of this method is to
     * "tap into" a method chain sequence in order to modify intermediate results.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Seq
     * @param {*} value The value to provide to `interceptor`.
     * @param {Function} interceptor The function to invoke.
     * @returns {*} Returns `value`.
     * @example
     *
     * _([1, 2, 3])
     *  .tap(function(array) {
     *    // Mutate input array.
     *    array.pop();
     *  })
     *  .reverse()
     *  .value();
     * // => [2, 1]
     */
    function tap(value, interceptor) {
      interceptor(value);
      return value;
    }

    /**
     * This method is like `_.tap` except that it returns the result of `interceptor`.
     * The purpose of this method is to "pass thru" values replacing intermediate
     * results in a method chain sequence.
     *
     * @static
     * @memberOf _
     * @since 3.0.0
     * @category Seq
     * @param {*} value The value to provide to `interceptor`.
     * @param {Function} interceptor The function to invoke.
     * @returns {*} Returns the result of `interceptor`.
     * @example
     *
     * _('  abc  ')
     *  .chain()
     *  .trim()
     *  .thru(function(value) {
     *    return [value];
     *  })
     *  .value();
     * // => ['abc']
     */
    function thru(value, interceptor) {
      return interceptor(value);
    }

    /**
     * This method is the wrapper version of `_.at`.
     *
     * @name at
     * @memberOf _
     * @since 1.0.0
     * @category Seq
     * @param {...(string|string[])} [paths] The property paths to pick.
     * @returns {Object} Returns the new `lodash` wrapper instance.
     * @example
     *
     * var object = { 'a': [{ 'b': { 'c': 3 } }, 4] };
     *
     * _(object).at(['a[0].b.c', 'a[1]']).value();
     * // => [3, 4]
     */
    var wrapperAt = flatRest(function(paths) {
      var length = paths.length,
          start = length ? paths[0] : 0,
          value = this.__wrapped__,
          interceptor = function(object) { return baseAt(object, paths); };

      if (length > 1 || this.__actions__.length ||
          !(value instanceof LazyWrapper) || !isIndex(start)) {
        return this.thru(interceptor);
      }
      value = value.slice(start, +start + (length ? 1 : 0));
      value.__actions__.push({
        'func': thru,
        'args': [interceptor],
        'thisArg': undefined
      });
      return new LodashWrapper(value, this.__chain__).thru(function(array) {
        if (length && !array.length) {
          array.push(undefined);
        }
        return array;
      });
    });

    /**
     * Creates a `lodash` wrapper instance with explicit method chain sequences enabled.
     *
     * @name chain
     * @memberOf _
     * @since 0.1.0
     * @category Seq
     * @returns {Object} Returns the new `lodash` wrapper instance.
     * @example
     *
     * var users = [
     *   { 'user': 'barney', 'age': 36 },
     *   { 'user': 'fred',   'age': 40 }
     * ];
     *
     * // A sequence without explicit chaining.
     * _(users).head();
     * // => { 'user': 'barney', 'age': 36 }
     *
     * // A sequence with explicit chaining.
     * _(users)
     *   .chain()
     *   .head()
     *   .pick('user')
     *   .value();
     * // => { 'user': 'barney' }
     */
    function wrapperChain() {
      return chain(this);
    }

    /**
     * Executes the chain sequence and returns the wrapped result.
     *
     * @name commit
     * @memberOf _
     * @since 3.2.0
     * @category Seq
     * @returns {Object} Returns the new `lodash` wrapper instance.
     * @example
     *
     * var array = [1, 2];
     * var wrapped = _(array).push(3);
     *
     * console.log(array);
     * // => [1, 2]
     *
     * wrapped = wrapped.commit();
     * console.log(array);
     * // => [1, 2, 3]
     *
     * wrapped.last();
     * // => 3
     *
     * console.log(array);
     * // => [1, 2, 3]
     */
    function wrapperCommit() {
      return new LodashWrapper(this.value(), this.__chain__);
    }

    /**
     * Gets the next value on a wrapped object following the
     * [iterator protocol](https://mdn.io/iteration_protocols#iterator).
     *
     * @name next
     * @memberOf _
     * @since 4.0.0
     * @category Seq
     * @returns {Object} Returns the next iterator value.
     * @example
     *
     * var wrapped = _([1, 2]);
     *
     * wrapped.next();
     * // => { 'done': false, 'value': 1 }
     *
     * wrapped.next();
     * // => { 'done': false, 'value': 2 }
     *
     * wrapped.next();
     * // => { 'done': true, 'value': undefined }
     */
    function wrapperNext() {
      if (this.__values__ === undefined) {
        this.__values__ = toArray(this.value());
      }
      var done = this.__index__ >= this.__values__.length,
          value = done ? undefined : this.__values__[this.__index__++];

      return { 'done': done, 'value': value };
    }

    /**
     * Enables the wrapper to be iterable.
     *
     * @name Symbol.iterator
     * @memberOf _
     * @since 4.0.0
     * @category Seq
     * @returns {Object} Returns the wrapper object.
     * @example
     *
     * var wrapped = _([1, 2]);
     *
     * wrapped[Symbol.iterator]() === wrapped;
     * // => true
     *
     * Array.from(wrapped);
     * // => [1, 2]
     */
    function wrapperToIterator() {
      return this;
    }

    /**
     * Creates a clone of the chain sequence planting `value` as the wrapped value.
     *
     * @name plant
     * @memberOf _
     * @since 3.2.0
     * @category Seq
     * @param {*} value The value to plant.
     * @returns {Object} Returns the new `lodash` wrapper instance.
     * @example
     *
     * function square(n) {
     *   return n * n;
     * }
     *
     * var wrapped = _([1, 2]).map(square);
     * var other = wrapped.plant([3, 4]);
     *
     * other.value();
     * // => [9, 16]
     *
     * wrapped.value();
     * // => [1, 4]
     */
    function wrapperPlant(value) {
      var result,
          parent = this;

      while (parent instanceof baseLodash) {
        var clone = wrapperClone(parent);
        clone.__index__ = 0;
        clone.__values__ = undefined;
        if (result) {
          previous.__wrapped__ = clone;
        } else {
          result = clone;
        }
        var previous = clone;
        parent = parent.__wrapped__;
      }
      previous.__wrapped__ = value;
      return result;
    }

    /**
     * This method is the wrapper version of `_.reverse`.
     *
     * **Note:** This method mutates the wrapped array.
     *
     * @name reverse
     * @memberOf _
     * @since 0.1.0
     * @category Seq
     * @returns {Object} Returns the new `lodash` wrapper instance.
     * @example
     *
     * var array = [1, 2, 3];
     *
     * _(array).reverse().value()
     * // => [3, 2, 1]
     *
     * console.log(array);
     * // => [3, 2, 1]
     */
    function wrapperReverse() {
      var value = this.__wrapped__;
      if (value instanceof LazyWrapper) {
        var wrapped = value;
        if (this.__actions__.length) {
          wrapped = new LazyWrapper(this);
        }
        wrapped = wrapped.reverse();
        wrapped.__actions__.push({
          'func': thru,
          'args': [reverse],
          'thisArg': undefined
        });
        return new LodashWrapper(wrapped, this.__chain__);
      }
      return this.thru(reverse);
    }

    /**
     * Executes the chain sequence to resolve the unwrapped value.
     *
     * @name value
     * @memberOf _
     * @since 0.1.0
     * @alias toJSON, valueOf
     * @category Seq
     * @returns {*} Returns the resolved unwrapped value.
     * @example
     *
     * _([1, 2, 3]).value();
     * // => [1, 2, 3]
     */
    function wrapperValue() {
      return baseWrapperValue(this.__wrapped__, this.__actions__);
    }

    /*------------------------------------------------------------------------*/

    /**
     * Creates an object composed of keys generated from the results of running
     * each element of `collection` thru `iteratee`. The corresponding value of
     * each key is the number of times the key was returned by `iteratee`. The
     * iteratee is invoked with one argument: (value).
     *
     * @static
     * @memberOf _
     * @since 0.5.0
     * @category Collection
     * @param {Array|Object} collection The collection to iterate over.
     * @param {Function} [iteratee=_.identity] The iteratee to transform keys.
     * @returns {Object} Returns the composed aggregate object.
     * @example
     *
     * _.countBy([6.1, 4.2, 6.3], Math.floor);
     * // => { '4': 1, '6': 2 }
     *
     * // The `_.property` iteratee shorthand.
     * _.countBy(['one', 'two', 'three'], 'length');
     * // => { '3': 2, '5': 1 }
     */
    var countBy = createAggregator(function(result, value, key) {
      if (hasOwnProperty.call(result, key)) {
        ++result[key];
      } else {
        baseAssignValue(result, key, 1);
      }
    });

    /**
     * Checks if `predicate` returns truthy for **all** elements of `collection`.
     * Iteration is stopped once `predicate` returns falsey. The predicate is
     * invoked with three arguments: (value, index|key, collection).
     *
     * **Note:** This method returns `true` for
     * [empty collections](https://en.wikipedia.org/wiki/Empty_set) because
     * [everything is true](https://en.wikipedia.org/wiki/Vacuous_truth) of
     * elements of empty collections.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Collection
     * @param {Array|Object} collection The collection to iterate over.
     * @param {Function} [predicate=_.identity] The function invoked per iteration.
     * @param- {Object} [guard] Enables use as an iteratee for methods like `_.map`.
     * @returns {boolean} Returns `true` if all elements pass the predicate check,
     *  else `false`.
     * @example
     *
     * _.every([true, 1, null, 'yes'], Boolean);
     * // => false
     *
     * var users = [
     *   { 'user': 'barney', 'age': 36, 'active': false },
     *   { 'user': 'fred',   'age': 40, 'active': false }
     * ];
     *
     * // The `_.matches` iteratee shorthand.
     * _.every(users, { 'user': 'barney', 'active': false });
     * // => false
     *
     * // The `_.matchesProperty` iteratee shorthand.
     * _.every(users, ['active', false]);
     * // => true
     *
     * // The `_.property` iteratee shorthand.
     * _.every(users, 'active');
     * // => false
     */
    function every(collection, predicate, guard) {
      var func = isArray(collection) ? arrayEvery : baseEvery;
      if (guard && isIterateeCall(collection, predicate, guard)) {
        predicate = undefined;
      }
      return func(collection, getIteratee(predicate, 3));
    }

    /**
     * Iterates over elements of `collection`, returning an array of all elements
     * `predicate` returns truthy for. The predicate is invoked with three
     * arguments: (value, index|key, collection).
     *
     * **Note:** Unlike `_.remove`, this method returns a new array.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Collection
     * @param {Array|Object} collection The collection to iterate over.
     * @param {Function} [predicate=_.identity] The function invoked per iteration.
     * @returns {Array} Returns the new filtered array.
     * @see _.reject
     * @example
     *
     * var users = [
     *   { 'user': 'barney', 'age': 36, 'active': true },
     *   { 'user': 'fred',   'age': 40, 'active': false }
     * ];
     *
     * _.filter(users, function(o) { return !o.active; });
     * // => objects for ['fred']
     *
     * // The `_.matches` iteratee shorthand.
     * _.filter(users, { 'age': 36, 'active': true });
     * // => objects for ['barney']
     *
     * // The `_.matchesProperty` iteratee shorthand.
     * _.filter(users, ['active', false]);
     * // => objects for ['fred']
     *
     * // The `_.property` iteratee shorthand.
     * _.filter(users, 'active');
     * // => objects for ['barney']
     *
     * // Combining several predicates using `_.overEvery` or `_.overSome`.
     * _.filter(users, _.overSome([{ 'age': 36 }, ['age', 40]]));
     * // => objects for ['fred', 'barney']
     */
    function filter(collection, predicate) {
      var func = isArray(collection) ? arrayFilter : baseFilter;
      return func(collection, getIteratee(predicate, 3));
    }

    /**
     * Iterates over elements of `collection`, returning the first element
     * `predicate` returns truthy for. The predicate is invoked with three
     * arguments: (value, index|key, collection).
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Collection
     * @param {Array|Object} collection The collection to inspect.
     * @param {Function} [predicate=_.identity] The function invoked per iteration.
     * @param {number} [fromIndex=0] The index to search from.
     * @returns {*} Returns the matched element, else `undefined`.
     * @example
     *
     * var users = [
     *   { 'user': 'barney',  'age': 36, 'active': true },
     *   { 'user': 'fred',    'age': 40, 'active': false },
     *   { 'user': 'pebbles', 'age': 1,  'active': true }
     * ];
     *
     * _.find(users, function(o) { return o.age < 40; });
     * // => object for 'barney'
     *
     * // The `_.matches` iteratee shorthand.
     * _.find(users, { 'age': 1, 'active': true });
     * // => object for 'pebbles'
     *
     * // The `_.matchesProperty` iteratee shorthand.
     * _.find(users, ['active', false]);
     * // => object for 'fred'
     *
     * // The `_.property` iteratee shorthand.
     * _.find(users, 'active');
     * // => object for 'barney'
     */
    var find = createFind(findIndex);

    /**
     * This method is like `_.find` except that it iterates over elements of
     * `collection` from right to left.
     *
     * @static
     * @memberOf _
     * @since 2.0.0
     * @category Collection
     * @param {Array|Object} collection The collection to inspect.
     * @param {Function} [predicate=_.identity] The function invoked per iteration.
     * @param {number} [fromIndex=collection.length-1] The index to search from.
     * @returns {*} Returns the matched element, else `undefined`.
     * @example
     *
     * _.findLast([1, 2, 3, 4], function(n) {
     *   return n % 2 == 1;
     * });
     * // => 3
     */
    var findLast = createFind(findLastIndex);

    /**
     * Creates a flattened array of values by running each element in `collection`
     * thru `iteratee` and flattening the mapped results. The iteratee is invoked
     * with three arguments: (value, index|key, collection).
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Collection
     * @param {Array|Object} collection The collection to iterate over.
     * @param {Function} [iteratee=_.identity] The function invoked per iteration.
     * @returns {Array} Returns the new flattened array.
     * @example
     *
     * function duplicate(n) {
     *   return [n, n];
     * }
     *
     * _.flatMap([1, 2], duplicate);
     * // => [1, 1, 2, 2]
     */
    function flatMap(collection, iteratee) {
      return baseFlatten(map(collection, iteratee), 1);
    }

    /**
     * This method is like `_.flatMap` except that it recursively flattens the
     * mapped results.
     *
     * @static
     * @memberOf _
     * @since 4.7.0
     * @category Collection
     * @param {Array|Object} collection The collection to iterate over.
     * @param {Function} [iteratee=_.identity] The function invoked per iteration.
     * @returns {Array} Returns the new flattened array.
     * @example
     *
     * function duplicate(n) {
     *   return [[[n, n]]];
     * }
     *
     * _.flatMapDeep([1, 2], duplicate);
     * // => [1, 1, 2, 2]
     */
    function flatMapDeep(collection, iteratee) {
      return baseFlatten(map(collection, iteratee), INFINITY);
    }

    /**
     * This method is like `_.flatMap` except that it recursively flattens the
     * mapped results up to `depth` times.
     *
     * @static
     * @memberOf _
     * @since 4.7.0
     * @category Collection
     * @param {Array|Object} collection The collection to iterate over.
     * @param {Function} [iteratee=_.identity] The function invoked per iteration.
     * @param {number} [depth=1] The maximum recursion depth.
     * @returns {Array} Returns the new flattened array.
     * @example
     *
     * function duplicate(n) {
     *   return [[[n, n]]];
     * }
     *
     * _.flatMapDepth([1, 2], duplicate, 2);
     * // => [[1, 1], [2, 2]]
     */
    function flatMapDepth(collection, iteratee, depth) {
      depth = depth === undefined ? 1 : toInteger(depth);
      return baseFlatten(map(collection, iteratee), depth);
    }

    /**
     * Iterates over elements of `collection` and invokes `iteratee` for each element.
     * The iteratee is invoked with three arguments: (value, index|key, collection).
     * Iteratee functions may exit iteration early by explicitly returning `false`.
     *
     * **Note:** As with other "Collections" methods, objects with a "length"
     * property are iterated like arrays. To avoid this behavior use `_.forIn`
     * or `_.forOwn` for object iteration.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @alias each
     * @category Collection
     * @param {Array|Object} collection The collection to iterate over.
     * @param {Function} [iteratee=_.identity] The function invoked per iteration.
     * @returns {Array|Object} Returns `collection`.
     * @see _.forEachRight
     * @example
     *
     * _.forEach([1, 2], function(value) {
     *   console.log(value);
     * });
     * // => Logs `1` then `2`.
     *
     * _.forEach({ 'a': 1, 'b': 2 }, function(value, key) {
     *   console.log(key);
     * });
     * // => Logs 'a' then 'b' (iteration order is not guaranteed).
     */
    function forEach(collection, iteratee) {
      var func = isArray(collection) ? arrayEach : baseEach;
      return func(collection, getIteratee(iteratee, 3));
    }

    /**
     * This method is like `_.forEach` except that it iterates over elements of
     * `collection` from right to left.
     *
     * @static
     * @memberOf _
     * @since 2.0.0
     * @alias eachRight
     * @category Collection
     * @param {Array|Object} collection The collection to iterate over.
     * @param {Function} [iteratee=_.identity] The function invoked per iteration.
     * @returns {Array|Object} Returns `collection`.
     * @see _.forEach
     * @example
     *
     * _.forEachRight([1, 2], function(value) {
     *   console.log(value);
     * });
     * // => Logs `2` then `1`.
     */
    function forEachRight(collection, iteratee) {
      var func = isArray(collection) ? arrayEachRight : baseEachRight;
      return func(collection, getIteratee(iteratee, 3));
    }

    /**
     * Creates an object composed of keys generated from the results of running
     * each element of `collection` thru `iteratee`. The order of grouped values
     * is determined by the order they occur in `collection`. The corresponding
     * value of each key is an array of elements responsible for generating the
     * key. The iteratee is invoked with one argument: (value).
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Collection
     * @param {Array|Object} collection The collection to iterate over.
     * @param {Function} [iteratee=_.identity] The iteratee to transform keys.
     * @returns {Object} Returns the composed aggregate object.
     * @example
     *
     * _.groupBy([6.1, 4.2, 6.3], Math.floor);
     * // => { '4': [4.2], '6': [6.1, 6.3] }
     *
     * // The `_.property` iteratee shorthand.
     * _.groupBy(['one', 'two', 'three'], 'length');
     * // => { '3': ['one', 'two'], '5': ['three'] }
     */
    var groupBy = createAggregator(function(result, value, key) {
      if (hasOwnProperty.call(result, key)) {
        result[key].push(value);
      } else {
        baseAssignValue(result, key, [value]);
      }
    });

    /**
     * Checks if `value` is in `collection`. If `collection` is a string, it's
     * checked for a substring of `value`, otherwise
     * [`SameValueZero`](http://ecma-international.org/ecma-262/7.0/#sec-samevaluezero)
     * is used for equality comparisons. If `fromIndex` is negative, it's used as
     * the offset from the end of `collection`.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Collection
     * @param {Array|Object|string} collection The collection to inspect.
     * @param {*} value The value to search for.
     * @param {number} [fromIndex=0] The index to search from.
     * @param- {Object} [guard] Enables use as an iteratee for methods like `_.reduce`.
     * @returns {boolean} Returns `true` if `value` is found, else `false`.
     * @example
     *
     * _.includes([1, 2, 3], 1);
     * // => true
     *
     * _.includes([1, 2, 3], 1, 2);
     * // => false
     *
     * _.includes({ 'a': 1, 'b': 2 }, 1);
     * // => true
     *
     * _.includes('abcd', 'bc');
     * // => true
     */
    function includes(collection, value, fromIndex, guard) {
      collection = isArrayLike(collection) ? collection : values(collection);
      fromIndex = (fromIndex && !guard) ? toInteger(fromIndex) : 0;

      var length = collection.length;
      if (fromIndex < 0) {
        fromIndex = nativeMax(length + fromIndex, 0);
      }
      return isString(collection)
        ? (fromIndex <= length && collection.indexOf(value, fromIndex) > -1)
        : (!!length && baseIndexOf(collection, value, fromIndex) > -1);
    }

    /**
     * Invokes the method at `path` of each element in `collection`, returning
     * an array of the results of each invoked method. Any additional arguments
     * are provided to each invoked method. If `path` is a function, it's invoked
     * for, and `this` bound to, each element in `collection`.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Collection
     * @param {Array|Object} collection The collection to iterate over.
     * @param {Array|Function|string} path The path of the method to invoke or
     *  the function invoked per iteration.
     * @param {...*} [args] The arguments to invoke each method with.
     * @returns {Array} Returns the array of results.
     * @example
     *
     * _.invokeMap([[5, 1, 7], [3, 2, 1]], 'sort');
     * // => [[1, 5, 7], [1, 2, 3]]
     *
     * _.invokeMap([123, 456], String.prototype.split, '');
     * // => [['1', '2', '3'], ['4', '5', '6']]
     */
    var invokeMap = baseRest(function(collection, path, args) {
      var index = -1,
          isFunc = typeof path == 'function',
          result = isArrayLike(collection) ? Array(collection.length) : [];

      baseEach(collection, function(value) {
        result[++index] = isFunc ? apply(path, value, args) : baseInvoke(value, path, args);
      });
      return result;
    });

    /**
     * Creates an object composed of keys generated from the results of running
     * each element of `collection` thru `iteratee`. The corresponding value of
     * each key is the last element responsible for generating the key. The
     * iteratee is invoked with one argument: (value).
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Collection
     * @param {Array|Object} collection The collection to iterate over.
     * @param {Function} [iteratee=_.identity] The iteratee to transform keys.
     * @returns {Object} Returns the composed aggregate object.
     * @example
     *
     * var array = [
     *   { 'dir': 'left', 'code': 97 },
     *   { 'dir': 'right', 'code': 100 }
     * ];
     *
     * _.keyBy(array, function(o) {
     *   return String.fromCharCode(o.code);
     * });
     * // => { 'a': { 'dir': 'left', 'code': 97 }, 'd': { 'dir': 'right', 'code': 100 } }
     *
     * _.keyBy(array, 'dir');
     * // => { 'left': { 'dir': 'left', 'code': 97 }, 'right': { 'dir': 'right', 'code': 100 } }
     */
    var keyBy = createAggregator(function(result, value, key) {
      baseAssignValue(result, key, value);
    });

    /**
     * Creates an array of values by running each element in `collection` thru
     * `iteratee`. The iteratee is invoked with three arguments:
     * (value, index|key, collection).
     *
     * Many lodash methods are guarded to work as iteratees for methods like
     * `_.every`, `_.filter`, `_.map`, `_.mapValues`, `_.reject`, and `_.some`.
     *
     * The guarded methods are:
     * `ary`, `chunk`, `curry`, `curryRight`, `drop`, `dropRight`, `every`,
     * `fill`, `invert`, `parseInt`, `random`, `range`, `rangeRight`, `repeat`,
     * `sampleSize`, `slice`, `some`, `sortBy`, `split`, `take`, `takeRight`,
     * `template`, `trim`, `trimEnd`, `trimStart`, and `words`
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Collection
     * @param {Array|Object} collection The collection to iterate over.
     * @param {Function} [iteratee=_.identity] The function invoked per iteration.
     * @returns {Array} Returns the new mapped array.
     * @example
     *
     * function square(n) {
     *   return n * n;
     * }
     *
     * _.map([4, 8], square);
     * // => [16, 64]
     *
     * _.map({ 'a': 4, 'b': 8 }, square);
     * // => [16, 64] (iteration order is not guaranteed)
     *
     * var users = [
     *   { 'user': 'barney' },
     *   { 'user': 'fred' }
     * ];
     *
     * // The `_.property` iteratee shorthand.
     * _.map(users, 'user');
     * // => ['barney', 'fred']
     */
    function map(collection, iteratee) {
      var func = isArray(collection) ? arrayMap : baseMap;
      return func(collection, getIteratee(iteratee, 3));
    }

    /**
     * This method is like `_.sortBy` except that it allows specifying the sort
     * orders of the iteratees to sort by. If `orders` is unspecified, all values
     * are sorted in ascending order. Otherwise, specify an order of "desc" for
     * descending or "asc" for ascending sort order of corresponding values.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Collection
     * @param {Array|Object} collection The collection to iterate over.
     * @param {Array[]|Function[]|Object[]|string[]} [iteratees=[_.identity]]
     *  The iteratees to sort by.
     * @param {string[]} [orders] The sort orders of `iteratees`.
     * @param- {Object} [guard] Enables use as an iteratee for methods like `_.reduce`.
     * @returns {Array} Returns the new sorted array.
     * @example
     *
     * var users = [
     *   { 'user': 'fred',   'age': 48 },
     *   { 'user': 'barney', 'age': 34 },
     *   { 'user': 'fred',   'age': 40 },
     *   { 'user': 'barney', 'age': 36 }
     * ];
     *
     * // Sort by `user` in ascending order and by `age` in descending order.
     * _.orderBy(users, ['user', 'age'], ['asc', 'desc']);
     * // => objects for [['barney', 36], ['barney', 34], ['fred', 48], ['fred', 40]]
     */
    function orderBy(collection, iteratees, orders, guard) {
      if (collection == null) {
        return [];
      }
      if (!isArray(iteratees)) {
        iteratees = iteratees == null ? [] : [iteratees];
      }
      orders = guard ? undefined : orders;
      if (!isArray(orders)) {
        orders = orders == null ? [] : [orders];
      }
      return baseOrderBy(collection, iteratees, orders);
    }

    /**
     * Creates an array of elements split into two groups, the first of which
     * contains elements `predicate` returns truthy for, the second of which
     * contains elements `predicate` returns falsey for. The predicate is
     * invoked with one argument: (value).
     *
     * @static
     * @memberOf _
     * @since 3.0.0
     * @category Collection
     * @param {Array|Object} collection The collection to iterate over.
     * @param {Function} [predicate=_.identity] The function invoked per iteration.
     * @returns {Array} Returns the array of grouped elements.
     * @example
     *
     * var users = [
     *   { 'user': 'barney',  'age': 36, 'active': false },
     *   { 'user': 'fred',    'age': 40, 'active': true },
     *   { 'user': 'pebbles', 'age': 1,  'active': false }
     * ];
     *
     * _.partition(users, function(o) { return o.active; });
     * // => objects for [['fred'], ['barney', 'pebbles']]
     *
     * // The `_.matches` iteratee shorthand.
     * _.partition(users, { 'age': 1, 'active': false });
     * // => objects for [['pebbles'], ['barney', 'fred']]
     *
     * // The `_.matchesProperty` iteratee shorthand.
     * _.partition(users, ['active', false]);
     * // => objects for [['barney', 'pebbles'], ['fred']]
     *
     * // The `_.property` iteratee shorthand.
     * _.partition(users, 'active');
     * // => objects for [['fred'], ['barney', 'pebbles']]
     */
    var partition = createAggregator(function(result, value, key) {
      result[key ? 0 : 1].push(value);
    }, function() { return [[], []]; });

    /**
     * Reduces `collection` to a value which is the accumulated result of running
     * each element in `collection` thru `iteratee`, where each successive
     * invocation is supplied the return value of the previous. If `accumulator`
     * is not given, the first element of `collection` is used as the initial
     * value. The iteratee is invoked with four arguments:
     * (accumulator, value, index|key, collection).
     *
     * Many lodash methods are guarded to work as iteratees for methods like
     * `_.reduce`, `_.reduceRight`, and `_.transform`.
     *
     * The guarded methods are:
     * `assign`, `defaults`, `defaultsDeep`, `includes`, `merge`, `orderBy`,
     * and `sortBy`
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Collection
     * @param {Array|Object} collection The collection to iterate over.
     * @param {Function} [iteratee=_.identity] The function invoked per iteration.
     * @param {*} [accumulator] The initial value.
     * @returns {*} Returns the accumulated value.
     * @see _.reduceRight
     * @example
     *
     * _.reduce([1, 2], function(sum, n) {
     *   return sum + n;
     * }, 0);
     * // => 3
     *
     * _.reduce({ 'a': 1, 'b': 2, 'c': 1 }, function(result, value, key) {
     *   (result[value] || (result[value] = [])).push(key);
     *   return result;
     * }, {});
     * // => { '1': ['a', 'c'], '2': ['b'] } (iteration order is not guaranteed)
     */
    function reduce(collection, iteratee, accumulator) {
      var func = isArray(collection) ? arrayReduce : baseReduce,
          initAccum = arguments.length < 3;

      return func(collection, getIteratee(iteratee, 4), accumulator, initAccum, baseEach);
    }

    /**
     * This method is like `_.reduce` except that it iterates over elements of
     * `collection` from right to left.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Collection
     * @param {Array|Object} collection The collection to iterate over.
     * @param {Function} [iteratee=_.identity] The function invoked per iteration.
     * @param {*} [accumulator] The initial value.
     * @returns {*} Returns the accumulated value.
     * @see _.reduce
     * @example
     *
     * var array = [[0, 1], [2, 3], [4, 5]];
     *
     * _.reduceRight(array, function(flattened, other) {
     *   return flattened.concat(other);
     * }, []);
     * // => [4, 5, 2, 3, 0, 1]
     */
    function reduceRight(collection, iteratee, accumulator) {
      var func = isArray(collection) ? arrayReduceRight : baseReduce,
          initAccum = arguments.length < 3;

      return func(collection, getIteratee(iteratee, 4), accumulator, initAccum, baseEachRight);
    }

    /**
     * The opposite of `_.filter`; this method returns the elements of `collection`
     * that `predicate` does **not** return truthy for.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Collection
     * @param {Array|Object} collection The collection to iterate over.
     * @param {Function} [predicate=_.identity] The function invoked per iteration.
     * @returns {Array} Returns the new filtered array.
     * @see _.filter
     * @example
     *
     * var users = [
     *   { 'user': 'barney', 'age': 36, 'active': false },
     *   { 'user': 'fred',   'age': 40, 'active': true }
     * ];
     *
     * _.reject(users, function(o) { return !o.active; });
     * // => objects for ['fred']
     *
     * // The `_.matches` iteratee shorthand.
     * _.reject(users, { 'age': 40, 'active': true });
     * // => objects for ['barney']
     *
     * // The `_.matchesProperty` iteratee shorthand.
     * _.reject(users, ['active', false]);
     * // => objects for ['fred']
     *
     * // The `_.property` iteratee shorthand.
     * _.reject(users, 'active');
     * // => objects for ['barney']
     */
    function reject(collection, predicate) {
      var func = isArray(collection) ? arrayFilter : baseFilter;
      return func(collection, negate(getIteratee(predicate, 3)));
    }

    /**
     * Gets a random element from `collection`.
     *
     * @static
     * @memberOf _
     * @since 2.0.0
     * @category Collection
     * @param {Array|Object} collection The collection to sample.
     * @returns {*} Returns the random element.
     * @example
     *
     * _.sample([1, 2, 3, 4]);
     * // => 2
     */
    function sample(collection) {
      var func = isArray(collection) ? arraySample : baseSample;
      return func(collection);
    }

    /**
     * Gets `n` random elements at unique keys from `collection` up to the
     * size of `collection`.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Collection
     * @param {Array|Object} collection The collection to sample.
     * @param {number} [n=1] The number of elements to sample.
     * @param- {Object} [guard] Enables use as an iteratee for methods like `_.map`.
     * @returns {Array} Returns the random elements.
     * @example
     *
     * _.sampleSize([1, 2, 3], 2);
     * // => [3, 1]
     *
     * _.sampleSize([1, 2, 3], 4);
     * // => [2, 3, 1]
     */
    function sampleSize(collection, n, guard) {
      if ((guard ? isIterateeCall(collection, n, guard) : n === undefined)) {
        n = 1;
      } else {
        n = toInteger(n);
      }
      var func = isArray(collection) ? arraySampleSize : baseSampleSize;
      return func(collection, n);
    }

    /**
     * Creates an array of shuffled values, using a version of the
     * [Fisher-Yates shuffle](https://en.wikipedia.org/wiki/Fisher-Yates_shuffle).
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Collection
     * @param {Array|Object} collection The collection to shuffle.
     * @returns {Array} Returns the new shuffled array.
     * @example
     *
     * _.shuffle([1, 2, 3, 4]);
     * // => [4, 1, 3, 2]
     */
    function shuffle(collection) {
      var func = isArray(collection) ? arrayShuffle : baseShuffle;
      return func(collection);
    }

    /**
     * Gets the size of `collection` by returning its length for array-like
     * values or the number of own enumerable string keyed properties for objects.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Collection
     * @param {Array|Object|string} collection The collection to inspect.
     * @returns {number} Returns the collection size.
     * @example
     *
     * _.size([1, 2, 3]);
     * // => 3
     *
     * _.size({ 'a': 1, 'b': 2 });
     * // => 2
     *
     * _.size('pebbles');
     * // => 7
     */
    function size(collection) {
      if (collection == null) {
        return 0;
      }
      if (isArrayLike(collection)) {
        return isString(collection) ? stringSize(collection) : collection.length;
      }
      var tag = getTag(collection);
      if (tag == mapTag || tag == setTag) {
        return collection.size;
      }
      return baseKeys(collection).length;
    }

    /**
     * Checks if `predicate` returns truthy for **any** element of `collection`.
     * Iteration is stopped once `predicate` returns truthy. The predicate is
     * invoked with three arguments: (value, index|key, collection).
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Collection
     * @param {Array|Object} collection The collection to iterate over.
     * @param {Function} [predicate=_.identity] The function invoked per iteration.
     * @param- {Object} [guard] Enables use as an iteratee for methods like `_.map`.
     * @returns {boolean} Returns `true` if any element passes the predicate check,
     *  else `false`.
     * @example
     *
     * _.some([null, 0, 'yes', false], Boolean);
     * // => true
     *
     * var users = [
     *   { 'user': 'barney', 'active': true },
     *   { 'user': 'fred',   'active': false }
     * ];
     *
     * // The `_.matches` iteratee shorthand.
     * _.some(users, { 'user': 'barney', 'active': false });
     * // => false
     *
     * // The `_.matchesProperty` iteratee shorthand.
     * _.some(users, ['active', false]);
     * // => true
     *
     * // The `_.property` iteratee shorthand.
     * _.some(users, 'active');
     * // => true
     */
    function some(collection, predicate, guard) {
      var func = isArray(collection) ? arraySome : baseSome;
      if (guard && isIterateeCall(collection, predicate, guard)) {
        predicate = undefined;
      }
      return func(collection, getIteratee(predicate, 3));
    }

    /**
     * Creates an array of elements, sorted in ascending order by the results of
     * running each element in a collection thru each iteratee. This method
     * performs a stable sort, that is, it preserves the original sort order of
     * equal elements. The iteratees are invoked with one argument: (value).
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Collection
     * @param {Array|Object} collection The collection to iterate over.
     * @param {...(Function|Function[])} [iteratees=[_.identity]]
     *  The iteratees to sort by.
     * @returns {Array} Returns the new sorted array.
     * @example
     *
     * var users = [
     *   { 'user': 'fred',   'age': 48 },
     *   { 'user': 'barney', 'age': 36 },
     *   { 'user': 'fred',   'age': 30 },
     *   { 'user': 'barney', 'age': 34 }
     * ];
     *
     * _.sortBy(users, [function(o) { return o.user; }]);
     * // => objects for [['barney', 36], ['barney', 34], ['fred', 48], ['fred', 30]]
     *
     * _.sortBy(users, ['user', 'age']);
     * // => objects for [['barney', 34], ['barney', 36], ['fred', 30], ['fred', 48]]
     */
    var sortBy = baseRest(function(collection, iteratees) {
      if (collection == null) {
        return [];
      }
      var length = iteratees.length;
      if (length > 1 && isIterateeCall(collection, iteratees[0], iteratees[1])) {
        iteratees = [];
      } else if (length > 2 && isIterateeCall(iteratees[0], iteratees[1], iteratees[2])) {
        iteratees = [iteratees[0]];
      }
      return baseOrderBy(collection, baseFlatten(iteratees, 1), []);
    });

    /*------------------------------------------------------------------------*/

    /**
     * Gets the timestamp of the number of milliseconds that have elapsed since
     * the Unix epoch (1 January 1970 00:00:00 UTC).
     *
     * @static
     * @memberOf _
     * @since 2.4.0
     * @category Date
     * @returns {number} Returns the timestamp.
     * @example
     *
     * _.defer(function(stamp) {
     *   console.log(_.now() - stamp);
     * }, _.now());
     * // => Logs the number of milliseconds it took for the deferred invocation.
     */
    var now = ctxNow || function() {
      return root.Date.now();
    };

    /*------------------------------------------------------------------------*/

    /**
     * The opposite of `_.before`; this method creates a function that invokes
     * `func` once it's called `n` or more times.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Function
     * @param {number} n The number of calls before `func` is invoked.
     * @param {Function} func The function to restrict.
     * @returns {Function} Returns the new restricted function.
     * @example
     *
     * var saves = ['profile', 'settings'];
     *
     * var done = _.after(saves.length, function() {
     *   console.log('done saving!');
     * });
     *
     * _.forEach(saves, function(type) {
     *   asyncSave({ 'type': type, 'complete': done });
     * });
     * // => Logs 'done saving!' after the two async saves have completed.
     */
    function after(n, func) {
      if (typeof func != 'function') {
        throw new TypeError(FUNC_ERROR_TEXT);
      }
      n = toInteger(n);
      return function() {
        if (--n < 1) {
          return func.apply(this, arguments);
        }
      };
    }

    /**
     * Creates a function that invokes `func`, with up to `n` arguments,
     * ignoring any additional arguments.
     *
     * @static
     * @memberOf _
     * @since 3.0.0
     * @category Function
     * @param {Function} func The function to cap arguments for.
     * @param {number} [n=func.length] The arity cap.
     * @param- {Object} [guard] Enables use as an iteratee for methods like `_.map`.
     * @returns {Function} Returns the new capped function.
     * @example
     *
     * _.map(['6', '8', '10'], _.ary(parseInt, 1));
     * // => [6, 8, 10]
     */
    function ary(func, n, guard) {
      n = guard ? undefined : n;
      n = (func && n == null) ? func.length : n;
      return createWrap(func, WRAP_ARY_FLAG, undefined, undefined, undefined, undefined, n);
    }

    /**
     * Creates a function that invokes `func`, with the `this` binding and arguments
     * of the created function, while it's called less than `n` times. Subsequent
     * calls to the created function return the result of the last `func` invocation.
     *
     * @static
     * @memberOf _
     * @since 3.0.0
     * @category Function
     * @param {number} n The number of calls at which `func` is no longer invoked.
     * @param {Function} func The function to restrict.
     * @returns {Function} Returns the new restricted function.
     * @example
     *
     * jQuery(element).on('click', _.before(5, addContactToList));
     * // => Allows adding up to 4 contacts to the list.
     */
    function before(n, func) {
      var result;
      if (typeof func != 'function') {
        throw new TypeError(FUNC_ERROR_TEXT);
      }
      n = toInteger(n);
      return function() {
        if (--n > 0) {
          result = func.apply(this, arguments);
        }
        if (n <= 1) {
          func = undefined;
        }
        return result;
      };
    }

    /**
     * Creates a function that invokes `func` with the `this` binding of `thisArg`
     * and `partials` prepended to the arguments it receives.
     *
     * The `_.bind.placeholder` value, which defaults to `_` in monolithic builds,
     * may be used as a placeholder for partially applied arguments.
     *
     * **Note:** Unlike native `Function#bind`, this method doesn't set the "length"
     * property of bound functions.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Function
     * @param {Function} func The function to bind.
     * @param {*} thisArg The `this` binding of `func`.
     * @param {...*} [partials] The arguments to be partially applied.
     * @returns {Function} Returns the new bound function.
     * @example
     *
     * function greet(greeting, punctuation) {
     *   return greeting + ' ' + this.user + punctuation;
     * }
     *
     * var object = { 'user': 'fred' };
     *
     * var bound = _.bind(greet, object, 'hi');
     * bound('!');
     * // => 'hi fred!'
     *
     * // Bound with placeholders.
     * var bound = _.bind(greet, object, _, '!');
     * bound('hi');
     * // => 'hi fred!'
     */
    var bind = baseRest(function(func, thisArg, partials) {
      var bitmask = WRAP_BIND_FLAG;
      if (partials.length) {
        var holders = replaceHolders(partials, getHolder(bind));
        bitmask |= WRAP_PARTIAL_FLAG;
      }
      return createWrap(func, bitmask, thisArg, partials, holders);
    });

    /**
     * Creates a function that invokes the method at `object[key]` with `partials`
     * prepended to the arguments it receives.
     *
     * This method differs from `_.bind` by allowing bound functions to reference
     * methods that may be redefined or don't yet exist. See
     * [Peter Michaux's article](http://peter.michaux.ca/articles/lazy-function-definition-pattern)
     * for more details.
     *
     * The `_.bindKey.placeholder` value, which defaults to `_` in monolithic
     * builds, may be used as a placeholder for partially applied arguments.
     *
     * @static
     * @memberOf _
     * @since 0.10.0
     * @category Function
     * @param {Object} object The object to invoke the method on.
     * @param {string} key The key of the method.
     * @param {...*} [partials] The arguments to be partially applied.
     * @returns {Function} Returns the new bound function.
     * @example
     *
     * var object = {
     *   'user': 'fred',
     *   'greet': function(greeting, punctuation) {
     *     return greeting + ' ' + this.user + punctuation;
     *   }
     * };
     *
     * var bound = _.bindKey(object, 'greet', 'hi');
     * bound('!');
     * // => 'hi fred!'
     *
     * object.greet = function(greeting, punctuation) {
     *   return greeting + 'ya ' + this.user + punctuation;
     * };
     *
     * bound('!');
     * // => 'hiya fred!'
     *
     * // Bound with placeholders.
     * var bound = _.bindKey(object, 'greet', _, '!');
     * bound('hi');
     * // => 'hiya fred!'
     */
    var bindKey = baseRest(function(object, key, partials) {
      var bitmask = WRAP_BIND_FLAG | WRAP_BIND_KEY_FLAG;
      if (partials.length) {
        var holders = replaceHolders(partials, getHolder(bindKey));
        bitmask |= WRAP_PARTIAL_FLAG;
      }
      return createWrap(key, bitmask, object, partials, holders);
    });

    /**
     * Creates a function that accepts arguments of `func` and either invokes
     * `func` returning its result, if at least `arity` number of arguments have
     * been provided, or returns a function that accepts the remaining `func`
     * arguments, and so on. The arity of `func` may be specified if `func.length`
     * is not sufficient.
     *
     * The `_.curry.placeholder` value, which defaults to `_` in monolithic builds,
     * may be used as a placeholder for provided arguments.
     *
     * **Note:** This method doesn't set the "length" property of curried functions.
     *
     * @static
     * @memberOf _
     * @since 2.0.0
     * @category Function
     * @param {Function} func The function to curry.
     * @param {number} [arity=func.length] The arity of `func`.
     * @param- {Object} [guard] Enables use as an iteratee for methods like `_.map`.
     * @returns {Function} Returns the new curried function.
     * @example
     *
     * var abc = function(a, b, c) {
     *   return [a, b, c];
     * };
     *
     * var curried = _.curry(abc);
     *
     * curried(1)(2)(3);
     * // => [1, 2, 3]
     *
     * curried(1, 2)(3);
     * // => [1, 2, 3]
     *
     * curried(1, 2, 3);
     * // => [1, 2, 3]
     *
     * // Curried with placeholders.
     * curried(1)(_, 3)(2);
     * // => [1, 2, 3]
     */
    function curry(func, arity, guard) {
      arity = guard ? undefined : arity;
      var result = createWrap(func, WRAP_CURRY_FLAG, undefined, undefined, undefined, undefined, undefined, arity);
      result.placeholder = curry.placeholder;
      return result;
    }

    /**
     * This method is like `_.curry` except that arguments are applied to `func`
     * in the manner of `_.partialRight` instead of `_.partial`.
     *
     * The `_.curryRight.placeholder` value, which defaults to `_` in monolithic
     * builds, may be used as a placeholder for provided arguments.
     *
     * **Note:** This method doesn't set the "length" property of curried functions.
     *
     * @static
     * @memberOf _
     * @since 3.0.0
     * @category Function
     * @param {Function} func The function to curry.
     * @param {number} [arity=func.length] The arity of `func`.
     * @param- {Object} [guard] Enables use as an iteratee for methods like `_.map`.
     * @returns {Function} Returns the new curried function.
     * @example
     *
     * var abc = function(a, b, c) {
     *   return [a, b, c];
     * };
     *
     * var curried = _.curryRight(abc);
     *
     * curried(3)(2)(1);
     * // => [1, 2, 3]
     *
     * curried(2, 3)(1);
     * // => [1, 2, 3]
     *
     * curried(1, 2, 3);
     * // => [1, 2, 3]
     *
     * // Curried with placeholders.
     * curried(3)(1, _)(2);
     * // => [1, 2, 3]
     */
    function curryRight(func, arity, guard) {
      arity = guard ? undefined : arity;
      var result = createWrap(func, WRAP_CURRY_RIGHT_FLAG, undefined, undefined, undefined, undefined, undefined, arity);
      result.placeholder = curryRight.placeholder;
      return result;
    }

    /**
     * Creates a debounced function that delays invoking `func` until after `wait`
     * milliseconds have elapsed since the last time the debounced function was
     * invoked. The debounced function comes with a `cancel` method to cancel
     * delayed `func` invocations and a `flush` method to immediately invoke them.
     * Provide `options` to indicate whether `func` should be invoked on the
     * leading and/or trailing edge of the `wait` timeout. The `func` is invoked
     * with the last arguments provided to the debounced function. Subsequent
     * calls to the debounced function return the result of the last `func`
     * invocation.
     *
     * **Note:** If `leading` and `trailing` options are `true`, `func` is
     * invoked on the trailing edge of the timeout only if the debounced function
     * is invoked more than once during the `wait` timeout.
     *
     * If `wait` is `0` and `leading` is `false`, `func` invocation is deferred
     * until to the next tick, similar to `setTimeout` with a timeout of `0`.
     *
     * See [David Corbacho's article](https://css-tricks.com/debouncing-throttling-explained-examples/)
     * for details over the differences between `_.debounce` and `_.throttle`.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Function
     * @param {Function} func The function to debounce.
     * @param {number} [wait=0] The number of milliseconds to delay.
     * @param {Object} [options={}] The options object.
     * @param {boolean} [options.leading=false]
     *  Specify invoking on the leading edge of the timeout.
     * @param {number} [options.maxWait]
     *  The maximum time `func` is allowed to be delayed before it's invoked.
     * @param {boolean} [options.trailing=true]
     *  Specify invoking on the trailing edge of the timeout.
     * @returns {Function} Returns the new debounced function.
     * @example
     *
     * // Avoid costly calculations while the window size is in flux.
     * jQuery(window).on('resize', _.debounce(calculateLayout, 150));
     *
     * // Invoke `sendMail` when clicked, debouncing subsequent calls.
     * jQuery(element).on('click', _.debounce(sendMail, 300, {
     *   'leading': true,
     *   'trailing': false
     * }));
     *
     * // Ensure `batchLog` is invoked once after 1 second of debounced calls.
     * var debounced = _.debounce(batchLog, 250, { 'maxWait': 1000 });
     * var source = new EventSource('/stream');
     * jQuery(source).on('message', debounced);
     *
     * // Cancel the trailing debounced invocation.
     * jQuery(window).on('popstate', debounced.cancel);
     */
    function debounce(func, wait, options) {
      var lastArgs,
          lastThis,
          maxWait,
          result,
          timerId,
          lastCallTime,
          lastInvokeTime = 0,
          leading = false,
          maxing = false,
          trailing = true;

      if (typeof func != 'function') {
        throw new TypeError(FUNC_ERROR_TEXT);
      }
      wait = toNumber(wait) || 0;
      if (isObject(options)) {
        leading = !!options.leading;
        maxing = 'maxWait' in options;
        maxWait = maxing ? nativeMax(toNumber(options.maxWait) || 0, wait) : maxWait;
        trailing = 'trailing' in options ? !!options.trailing : trailing;
      }

      function invokeFunc(time) {
        var args = lastArgs,
            thisArg = lastThis;

        lastArgs = lastThis = undefined;
        lastInvokeTime = time;
        result = func.apply(thisArg, args);
        return result;
      }

      function leadingEdge(time) {
        // Reset any `maxWait` timer.
        lastInvokeTime = time;
        // Start the timer for the trailing edge.
        timerId = setTimeout(timerExpired, wait);
        // Invoke the leading edge.
        return leading ? invokeFunc(time) : result;
      }

      function remainingWait(time) {
        var timeSinceLastCall = time - lastCallTime,
            timeSinceLastInvoke = time - lastInvokeTime,
            timeWaiting = wait - timeSinceLastCall;

        return maxing
          ? nativeMin(timeWaiting, maxWait - timeSinceLastInvoke)
          : timeWaiting;
      }

      function shouldInvoke(time) {
        var timeSinceLastCall = time - lastCallTime,
            timeSinceLastInvoke = time - lastInvokeTime;

        // Either this is the first call, activity has stopped and we're at the
        // trailing edge, the system time has gone backwards and we're treating
        // it as the trailing edge, or we've hit the `maxWait` limit.
        return (lastCallTime === undefined || (timeSinceLastCall >= wait) ||
          (timeSinceLastCall < 0) || (maxing && timeSinceLastInvoke >= maxWait));
      }

      function timerExpired() {
        var time = now();
        if (shouldInvoke(time)) {
          return trailingEdge(time);
        }
        // Restart the timer.
        timerId = setTimeout(timerExpired, remainingWait(time));
      }

      function trailingEdge(time) {
        timerId = undefined;

        // Only invoke if we have `lastArgs` which means `func` has been
        // debounced at least once.
        if (trailing && lastArgs) {
          return invokeFunc(time);
        }
        lastArgs = lastThis = undefined;
        return result;
      }

      function cancel() {
        if (timerId !== undefined) {
          clearTimeout(timerId);
        }
        lastInvokeTime = 0;
        lastArgs = lastCallTime = lastThis = timerId = undefined;
      }

      function flush() {
        return timerId === undefined ? result : trailingEdge(now());
      }

      function debounced() {
        var time = now(),
            isInvoking = shouldInvoke(time);

        lastArgs = arguments;
        lastThis = this;
        lastCallTime = time;

        if (isInvoking) {
          if (timerId === undefined) {
            return leadingEdge(lastCallTime);
          }
          if (maxing) {
            // Handle invocations in a tight loop.
            clearTimeout(timerId);
            timerId = setTimeout(timerExpired, wait);
            return invokeFunc(lastCallTime);
          }
        }
        if (timerId === undefined) {
          timerId = setTimeout(timerExpired, wait);
        }
        return result;
      }
      debounced.cancel = cancel;
      debounced.flush = flush;
      return debounced;
    }

    /**
     * Defers invoking the `func` until the current call stack has cleared. Any
     * additional arguments are provided to `func` when it's invoked.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Function
     * @param {Function} func The function to defer.
     * @param {...*} [args] The arguments to invoke `func` with.
     * @returns {number} Returns the timer id.
     * @example
     *
     * _.defer(function(text) {
     *   console.log(text);
     * }, 'deferred');
     * // => Logs 'deferred' after one millisecond.
     */
    var defer = baseRest(function(func, args) {
      return baseDelay(func, 1, args);
    });

    /**
     * Invokes `func` after `wait` milliseconds. Any additional arguments are
     * provided to `func` when it's invoked.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Function
     * @param {Function} func The function to delay.
     * @param {number} wait The number of milliseconds to delay invocation.
     * @param {...*} [args] The arguments to invoke `func` with.
     * @returns {number} Returns the timer id.
     * @example
     *
     * _.delay(function(text) {
     *   console.log(text);
     * }, 1000, 'later');
     * // => Logs 'later' after one second.
     */
    var delay = baseRest(function(func, wait, args) {
      return baseDelay(func, toNumber(wait) || 0, args);
    });

    /**
     * Creates a function that invokes `func` with arguments reversed.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Function
     * @param {Function} func The function to flip arguments for.
     * @returns {Function} Returns the new flipped function.
     * @example
     *
     * var flipped = _.flip(function() {
     *   return _.toArray(arguments);
     * });
     *
     * flipped('a', 'b', 'c', 'd');
     * // => ['d', 'c', 'b', 'a']
     */
    function flip(func) {
      return createWrap(func, WRAP_FLIP_FLAG);
    }

    /**
     * Creates a function that memoizes the result of `func`. If `resolver` is
     * provided, it determines the cache key for storing the result based on the
     * arguments provided to the memoized function. By default, the first argument
     * provided to the memoized function is used as the map cache key. The `func`
     * is invoked with the `this` binding of the memoized function.
     *
     * **Note:** The cache is exposed as the `cache` property on the memoized
     * function. Its creation may be customized by replacing the `_.memoize.Cache`
     * constructor with one whose instances implement the
     * [`Map`](http://ecma-international.org/ecma-262/7.0/#sec-properties-of-the-map-prototype-object)
     * method interface of `clear`, `delete`, `get`, `has`, and `set`.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Function
     * @param {Function} func The function to have its output memoized.
     * @param {Function} [resolver] The function to resolve the cache key.
     * @returns {Function} Returns the new memoized function.
     * @example
     *
     * var object = { 'a': 1, 'b': 2 };
     * var other = { 'c': 3, 'd': 4 };
     *
     * var values = _.memoize(_.values);
     * values(object);
     * // => [1, 2]
     *
     * values(other);
     * // => [3, 4]
     *
     * object.a = 2;
     * values(object);
     * // => [1, 2]
     *
     * // Modify the result cache.
     * values.cache.set(object, ['a', 'b']);
     * values(object);
     * // => ['a', 'b']
     *
     * // Replace `_.memoize.Cache`.
     * _.memoize.Cache = WeakMap;
     */
    function memoize(func, resolver) {
      if (typeof func != 'function' || (resolver != null && typeof resolver != 'function')) {
        throw new TypeError(FUNC_ERROR_TEXT);
      }
      var memoized = function() {
        var args = arguments,
            key = resolver ? resolver.apply(this, args) : args[0],
            cache = memoized.cache;

        if (cache.has(key)) {
          return cache.get(key);
        }
        var result = func.apply(this, args);
        memoized.cache = cache.set(key, result) || cache;
        return result;
      };
      memoized.cache = new (memoize.Cache || MapCache);
      return memoized;
    }

    // Expose `MapCache`.
    memoize.Cache = MapCache;

    /**
     * Creates a function that negates the result of the predicate `func`. The
     * `func` predicate is invoked with the `this` binding and arguments of the
     * created function.
     *
     * @static
     * @memberOf _
     * @since 3.0.0
     * @category Function
     * @param {Function} predicate The predicate to negate.
     * @returns {Function} Returns the new negated function.
     * @example
     *
     * function isEven(n) {
     *   return n % 2 == 0;
     * }
     *
     * _.filter([1, 2, 3, 4, 5, 6], _.negate(isEven));
     * // => [1, 3, 5]
     */
    function negate(predicate) {
      if (typeof predicate != 'function') {
        throw new TypeError(FUNC_ERROR_TEXT);
      }
      return function() {
        var args = arguments;
        switch (args.length) {
          case 0: return !predicate.call(this);
          case 1: return !predicate.call(this, args[0]);
          case 2: return !predicate.call(this, args[0], args[1]);
          case 3: return !predicate.call(this, args[0], args[1], args[2]);
        }
        return !predicate.apply(this, args);
      };
    }

    /**
     * Creates a function that is restricted to invoking `func` once. Repeat calls
     * to the function return the value of the first invocation. The `func` is
     * invoked with the `this` binding and arguments of the created function.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Function
     * @param {Function} func The function to restrict.
     * @returns {Function} Returns the new restricted function.
     * @example
     *
     * var initialize = _.once(createApplication);
     * initialize();
     * initialize();
     * // => `createApplication` is invoked once
     */
    function once(func) {
      return before(2, func);
    }

    /**
     * Creates a function that invokes `func` with its arguments transformed.
     *
     * @static
     * @since 4.0.0
     * @memberOf _
     * @category Function
     * @param {Function} func The function to wrap.
     * @param {...(Function|Function[])} [transforms=[_.identity]]
     *  The argument transforms.
     * @returns {Function} Returns the new function.
     * @example
     *
     * function doubled(n) {
     *   return n * 2;
     * }
     *
     * function square(n) {
     *   return n * n;
     * }
     *
     * var func = _.overArgs(function(x, y) {
     *   return [x, y];
     * }, [square, doubled]);
     *
     * func(9, 3);
     * // => [81, 6]
     *
     * func(10, 5);
     * // => [100, 10]
     */
    var overArgs = castRest(function(func, transforms) {
      transforms = (transforms.length == 1 && isArray(transforms[0]))
        ? arrayMap(transforms[0], baseUnary(getIteratee()))
        : arrayMap(baseFlatten(transforms, 1), baseUnary(getIteratee()));

      var funcsLength = transforms.length;
      return baseRest(function(args) {
        var index = -1,
            length = nativeMin(args.length, funcsLength);

        while (++index < length) {
          args[index] = transforms[index].call(this, args[index]);
        }
        return apply(func, this, args);
      });
    });

    /**
     * Creates a function that invokes `func` with `partials` prepended to the
     * arguments it receives. This method is like `_.bind` except it does **not**
     * alter the `this` binding.
     *
     * The `_.partial.placeholder` value, which defaults to `_` in monolithic
     * builds, may be used as a placeholder for partially applied arguments.
     *
     * **Note:** This method doesn't set the "length" property of partially
     * applied functions.
     *
     * @static
     * @memberOf _
     * @since 0.2.0
     * @category Function
     * @param {Function} func The function to partially apply arguments to.
     * @param {...*} [partials] The arguments to be partially applied.
     * @returns {Function} Returns the new partially applied function.
     * @example
     *
     * function greet(greeting, name) {
     *   return greeting + ' ' + name;
     * }
     *
     * var sayHelloTo = _.partial(greet, 'hello');
     * sayHelloTo('fred');
     * // => 'hello fred'
     *
     * // Partially applied with placeholders.
     * var greetFred = _.partial(greet, _, 'fred');
     * greetFred('hi');
     * // => 'hi fred'
     */
    var partial = baseRest(function(func, partials) {
      var holders = replaceHolders(partials, getHolder(partial));
      return createWrap(func, WRAP_PARTIAL_FLAG, undefined, partials, holders);
    });

    /**
     * This method is like `_.partial` except that partially applied arguments
     * are appended to the arguments it receives.
     *
     * The `_.partialRight.placeholder` value, which defaults to `_` in monolithic
     * builds, may be used as a placeholder for partially applied arguments.
     *
     * **Note:** This method doesn't set the "length" property of partially
     * applied functions.
     *
     * @static
     * @memberOf _
     * @since 1.0.0
     * @category Function
     * @param {Function} func The function to partially apply arguments to.
     * @param {...*} [partials] The arguments to be partially applied.
     * @returns {Function} Returns the new partially applied function.
     * @example
     *
     * function greet(greeting, name) {
     *   return greeting + ' ' + name;
     * }
     *
     * var greetFred = _.partialRight(greet, 'fred');
     * greetFred('hi');
     * // => 'hi fred'
     *
     * // Partially applied with placeholders.
     * var sayHelloTo = _.partialRight(greet, 'hello', _);
     * sayHelloTo('fred');
     * // => 'hello fred'
     */
    var partialRight = baseRest(function(func, partials) {
      var holders = replaceHolders(partials, getHolder(partialRight));
      return createWrap(func, WRAP_PARTIAL_RIGHT_FLAG, undefined, partials, holders);
    });

    /**
     * Creates a function that invokes `func` with arguments arranged according
     * to the specified `indexes` where the argument value at the first index is
     * provided as the first argument, the argument value at the second index is
     * provided as the second argument, and so on.
     *
     * @static
     * @memberOf _
     * @since 3.0.0
     * @category Function
     * @param {Function} func The function to rearrange arguments for.
     * @param {...(number|number[])} indexes The arranged argument indexes.
     * @returns {Function} Returns the new function.
     * @example
     *
     * var rearged = _.rearg(function(a, b, c) {
     *   return [a, b, c];
     * }, [2, 0, 1]);
     *
     * rearged('b', 'c', 'a')
     * // => ['a', 'b', 'c']
     */
    var rearg = flatRest(function(func, indexes) {
      return createWrap(func, WRAP_REARG_FLAG, undefined, undefined, undefined, indexes);
    });

    /**
     * Creates a function that invokes `func` with the `this` binding of the
     * created function and arguments from `start` and beyond provided as
     * an array.
     *
     * **Note:** This method is based on the
     * [rest parameter](https://mdn.io/rest_parameters).
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Function
     * @param {Function} func The function to apply a rest parameter to.
     * @param {number} [start=func.length-1] The start position of the rest parameter.
     * @returns {Function} Returns the new function.
     * @example
     *
     * var say = _.rest(function(what, names) {
     *   return what + ' ' + _.initial(names).join(', ') +
     *     (_.size(names) > 1 ? ', & ' : '') + _.last(names);
     * });
     *
     * say('hello', 'fred', 'barney', 'pebbles');
     * // => 'hello fred, barney, & pebbles'
     */
    function rest(func, start) {
      if (typeof func != 'function') {
        throw new TypeError(FUNC_ERROR_TEXT);
      }
      start = start === undefined ? start : toInteger(start);
      return baseRest(func, start);
    }

    /**
     * Creates a function that invokes `func` with the `this` binding of the
     * create function and an array of arguments much like
     * [`Function#apply`](http://www.ecma-international.org/ecma-262/7.0/#sec-function.prototype.apply).
     *
     * **Note:** This method is based on the
     * [spread operator](https://mdn.io/spread_operator).
     *
     * @static
     * @memberOf _
     * @since 3.2.0
     * @category Function
     * @param {Function} func The function to spread arguments over.
     * @param {number} [start=0] The start position of the spread.
     * @returns {Function} Returns the new function.
     * @example
     *
     * var say = _.spread(function(who, what) {
     *   return who + ' says ' + what;
     * });
     *
     * say(['fred', 'hello']);
     * // => 'fred says hello'
     *
     * var numbers = Promise.all([
     *   Promise.resolve(40),
     *   Promise.resolve(36)
     * ]);
     *
     * numbers.then(_.spread(function(x, y) {
     *   return x + y;
     * }));
     * // => a Promise of 76
     */
    function spread(func, start) {
      if (typeof func != 'function') {
        throw new TypeError(FUNC_ERROR_TEXT);
      }
      start = start == null ? 0 : nativeMax(toInteger(start), 0);
      return baseRest(function(args) {
        var array = args[start],
            otherArgs = castSlice(args, 0, start);

        if (array) {
          arrayPush(otherArgs, array);
        }
        return apply(func, this, otherArgs);
      });
    }

    /**
     * Creates a throttled function that only invokes `func` at most once per
     * every `wait` milliseconds. The throttled function comes with a `cancel`
     * method to cancel delayed `func` invocations and a `flush` method to
     * immediately invoke them. Provide `options` to indicate whether `func`
     * should be invoked on the leading and/or trailing edge of the `wait`
     * timeout. The `func` is invoked with the last arguments provided to the
     * throttled function. Subsequent calls to the throttled function return the
     * result of the last `func` invocation.
     *
     * **Note:** If `leading` and `trailing` options are `true`, `func` is
     * invoked on the trailing edge of the timeout only if the throttled function
     * is invoked more than once during the `wait` timeout.
     *
     * If `wait` is `0` and `leading` is `false`, `func` invocation is deferred
     * until to the next tick, similar to `setTimeout` with a timeout of `0`.
     *
     * See [David Corbacho's article](https://css-tricks.com/debouncing-throttling-explained-examples/)
     * for details over the differences between `_.throttle` and `_.debounce`.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Function
     * @param {Function} func The function to throttle.
     * @param {number} [wait=0] The number of milliseconds to throttle invocations to.
     * @param {Object} [options={}] The options object.
     * @param {boolean} [options.leading=true]
     *  Specify invoking on the leading edge of the timeout.
     * @param {boolean} [options.trailing=true]
     *  Specify invoking on the trailing edge of the timeout.
     * @returns {Function} Returns the new throttled function.
     * @example
     *
     * // Avoid excessively updating the position while scrolling.
     * jQuery(window).on('scroll', _.throttle(updatePosition, 100));
     *
     * // Invoke `renewToken` when the click event is fired, but not more than once every 5 minutes.
     * var throttled = _.throttle(renewToken, 300000, { 'trailing': false });
     * jQuery(element).on('click', throttled);
     *
     * // Cancel the trailing throttled invocation.
     * jQuery(window).on('popstate', throttled.cancel);
     */
    function throttle(func, wait, options) {
      var leading = true,
          trailing = true;

      if (typeof func != 'function') {
        throw new TypeError(FUNC_ERROR_TEXT);
      }
      if (isObject(options)) {
        leading = 'leading' in options ? !!options.leading : leading;
        trailing = 'trailing' in options ? !!options.trailing : trailing;
      }
      return debounce(func, wait, {
        'leading': leading,
        'maxWait': wait,
        'trailing': trailing
      });
    }

    /**
     * Creates a function that accepts up to one argument, ignoring any
     * additional arguments.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Function
     * @param {Function} func The function to cap arguments for.
     * @returns {Function} Returns the new capped function.
     * @example
     *
     * _.map(['6', '8', '10'], _.unary(parseInt));
     * // => [6, 8, 10]
     */
    function unary(func) {
      return ary(func, 1);
    }

    /**
     * Creates a function that provides `value` to `wrapper` as its first
     * argument. Any additional arguments provided to the function are appended
     * to those provided to the `wrapper`. The wrapper is invoked with the `this`
     * binding of the created function.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Function
     * @param {*} value The value to wrap.
     * @param {Function} [wrapper=identity] The wrapper function.
     * @returns {Function} Returns the new function.
     * @example
     *
     * var p = _.wrap(_.escape, function(func, text) {
     *   return '<p>' + func(text) + '</p>';
     * });
     *
     * p('fred, barney, & pebbles');
     * // => '<p>fred, barney, &amp; pebbles</p>'
     */
    function wrap(value, wrapper) {
      return partial(castFunction(wrapper), value);
    }

    /*------------------------------------------------------------------------*/

    /**
     * Casts `value` as an array if it's not one.
     *
     * @static
     * @memberOf _
     * @since 4.4.0
     * @category Lang
     * @param {*} value The value to inspect.
     * @returns {Array} Returns the cast array.
     * @example
     *
     * _.castArray(1);
     * // => [1]
     *
     * _.castArray({ 'a': 1 });
     * // => [{ 'a': 1 }]
     *
     * _.castArray('abc');
     * // => ['abc']
     *
     * _.castArray(null);
     * // => [null]
     *
     * _.castArray(undefined);
     * // => [undefined]
     *
     * _.castArray();
     * // => []
     *
     * var array = [1, 2, 3];
     * console.log(_.castArray(array) === array);
     * // => true
     */
    function castArray() {
      if (!arguments.length) {
        return [];
      }
      var value = arguments[0];
      return isArray(value) ? value : [value];
    }

    /**
     * Creates a shallow clone of `value`.
     *
     * **Note:** This method is loosely based on the
     * [structured clone algorithm](https://mdn.io/Structured_clone_algorithm)
     * and supports cloning arrays, array buffers, booleans, date objects, maps,
     * numbers, `Object` objects, regexes, sets, strings, symbols, and typed
     * arrays. The own enumerable properties of `arguments` objects are cloned
     * as plain objects. An empty object is returned for uncloneable values such
     * as error objects, functions, DOM nodes, and WeakMaps.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Lang
     * @param {*} value The value to clone.
     * @returns {*} Returns the cloned value.
     * @see _.cloneDeep
     * @example
     *
     * var objects = [{ 'a': 1 }, { 'b': 2 }];
     *
     * var shallow = _.clone(objects);
     * console.log(shallow[0] === objects[0]);
     * // => true
     */
    function clone(value) {
      return baseClone(value, CLONE_SYMBOLS_FLAG);
    }

    /**
     * This method is like `_.clone` except that it accepts `customizer` which
     * is invoked to produce the cloned value. If `customizer` returns `undefined`,
     * cloning is handled by the method instead. The `customizer` is invoked with
     * up to four arguments; (value [, index|key, object, stack]).
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Lang
     * @param {*} value The value to clone.
     * @param {Function} [customizer] The function to customize cloning.
     * @returns {*} Returns the cloned value.
     * @see _.cloneDeepWith
     * @example
     *
     * function customizer(value) {
     *   if (_.isElement(value)) {
     *     return value.cloneNode(false);
     *   }
     * }
     *
     * var el = _.cloneWith(document.body, customizer);
     *
     * console.log(el === document.body);
     * // => false
     * console.log(el.nodeName);
     * // => 'BODY'
     * console.log(el.childNodes.length);
     * // => 0
     */
    function cloneWith(value, customizer) {
      customizer = typeof customizer == 'function' ? customizer : undefined;
      return baseClone(value, CLONE_SYMBOLS_FLAG, customizer);
    }

    /**
     * This method is like `_.clone` except that it recursively clones `value`.
     *
     * @static
     * @memberOf _
     * @since 1.0.0
     * @category Lang
     * @param {*} value The value to recursively clone.
     * @returns {*} Returns the deep cloned value.
     * @see _.clone
     * @example
     *
     * var objects = [{ 'a': 1 }, { 'b': 2 }];
     *
     * var deep = _.cloneDeep(objects);
     * console.log(deep[0] === objects[0]);
     * // => false
     */
    function cloneDeep(value) {
      return baseClone(value, CLONE_DEEP_FLAG | CLONE_SYMBOLS_FLAG);
    }

    /**
     * This method is like `_.cloneWith` except that it recursively clones `value`.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Lang
     * @param {*} value The value to recursively clone.
     * @param {Function} [customizer] The function to customize cloning.
     * @returns {*} Returns the deep cloned value.
     * @see _.cloneWith
     * @example
     *
     * function customizer(value) {
     *   if (_.isElement(value)) {
     *     return value.cloneNode(true);
     *   }
     * }
     *
     * var el = _.cloneDeepWith(document.body, customizer);
     *
     * console.log(el === document.body);
     * // => false
     * console.log(el.nodeName);
     * // => 'BODY'
     * console.log(el.childNodes.length);
     * // => 20
     */
    function cloneDeepWith(value, customizer) {
      customizer = typeof customizer == 'function' ? customizer : undefined;
      return baseClone(value, CLONE_DEEP_FLAG | CLONE_SYMBOLS_FLAG, customizer);
    }

    /**
     * Checks if `object` conforms to `source` by invoking the predicate
     * properties of `source` with the corresponding property values of `object`.
     *
     * **Note:** This method is equivalent to `_.conforms` when `source` is
     * partially applied.
     *
     * @static
     * @memberOf _
     * @since 4.14.0
     * @category Lang
     * @param {Object} object The object to inspect.
     * @param {Object} source The object of property predicates to conform to.
     * @returns {boolean} Returns `true` if `object` conforms, else `false`.
     * @example
     *
     * var object = { 'a': 1, 'b': 2 };
     *
     * _.conformsTo(object, { 'b': function(n) { return n > 1; } });
     * // => true
     *
     * _.conformsTo(object, { 'b': function(n) { return n > 2; } });
     * // => false
     */
    function conformsTo(object, source) {
      return source == null || baseConformsTo(object, source, keys(source));
    }

    /**
     * Performs a
     * [`SameValueZero`](http://ecma-international.org/ecma-262/7.0/#sec-samevaluezero)
     * comparison between two values to determine if they are equivalent.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Lang
     * @param {*} value The value to compare.
     * @param {*} other The other value to compare.
     * @returns {boolean} Returns `true` if the values are equivalent, else `false`.
     * @example
     *
     * var object = { 'a': 1 };
     * var other = { 'a': 1 };
     *
     * _.eq(object, object);
     * // => true
     *
     * _.eq(object, other);
     * // => false
     *
     * _.eq('a', 'a');
     * // => true
     *
     * _.eq('a', Object('a'));
     * // => false
     *
     * _.eq(NaN, NaN);
     * // => true
     */
    function eq(value, other) {
      return value === other || (value !== value && other !== other);
    }

    /**
     * Checks if `value` is greater than `other`.
     *
     * @static
     * @memberOf _
     * @since 3.9.0
     * @category Lang
     * @param {*} value The value to compare.
     * @param {*} other The other value to compare.
     * @returns {boolean} Returns `true` if `value` is greater than `other`,
     *  else `false`.
     * @see _.lt
     * @example
     *
     * _.gt(3, 1);
     * // => true
     *
     * _.gt(3, 3);
     * // => false
     *
     * _.gt(1, 3);
     * // => false
     */
    var gt = createRelationalOperation(baseGt);

    /**
     * Checks if `value` is greater than or equal to `other`.
     *
     * @static
     * @memberOf _
     * @since 3.9.0
     * @category Lang
     * @param {*} value The value to compare.
     * @param {*} other The other value to compare.
     * @returns {boolean} Returns `true` if `value` is greater than or equal to
     *  `other`, else `false`.
     * @see _.lte
     * @example
     *
     * _.gte(3, 1);
     * // => true
     *
     * _.gte(3, 3);
     * // => true
     *
     * _.gte(1, 3);
     * // => false
     */
    var gte = createRelationalOperation(function(value, other) {
      return value >= other;
    });

    /**
     * Checks if `value` is likely an `arguments` object.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Lang
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is an `arguments` object,
     *  else `false`.
     * @example
     *
     * _.isArguments(function() { return arguments; }());
     * // => true
     *
     * _.isArguments([1, 2, 3]);
     * // => false
     */
    var isArguments = baseIsArguments(function() { return arguments; }()) ? baseIsArguments : function(value) {
      return isObjectLike(value) && hasOwnProperty.call(value, 'callee') &&
        !propertyIsEnumerable.call(value, 'callee');
    };

    /**
     * Checks if `value` is classified as an `Array` object.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Lang
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is an array, else `false`.
     * @example
     *
     * _.isArray([1, 2, 3]);
     * // => true
     *
     * _.isArray(document.body.children);
     * // => false
     *
     * _.isArray('abc');
     * // => false
     *
     * _.isArray(_.noop);
     * // => false
     */
    var isArray = Array.isArray;

    /**
     * Checks if `value` is classified as an `ArrayBuffer` object.
     *
     * @static
     * @memberOf _
     * @since 4.3.0
     * @category Lang
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is an array buffer, else `false`.
     * @example
     *
     * _.isArrayBuffer(new ArrayBuffer(2));
     * // => true
     *
     * _.isArrayBuffer(new Array(2));
     * // => false
     */
    var isArrayBuffer = nodeIsArrayBuffer ? baseUnary(nodeIsArrayBuffer) : baseIsArrayBuffer;

    /**
     * Checks if `value` is array-like. A value is considered array-like if it's
     * not a function and has a `value.length` that's an integer greater than or
     * equal to `0` and less than or equal to `Number.MAX_SAFE_INTEGER`.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Lang
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is array-like, else `false`.
     * @example
     *
     * _.isArrayLike([1, 2, 3]);
     * // => true
     *
     * _.isArrayLike(document.body.children);
     * // => true
     *
     * _.isArrayLike('abc');
     * // => true
     *
     * _.isArrayLike(_.noop);
     * // => false
     */
    function isArrayLike(value) {
      return value != null && isLength(value.length) && !isFunction(value);
    }

    /**
     * This method is like `_.isArrayLike` except that it also checks if `value`
     * is an object.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Lang
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is an array-like object,
     *  else `false`.
     * @example
     *
     * _.isArrayLikeObject([1, 2, 3]);
     * // => true
     *
     * _.isArrayLikeObject(document.body.children);
     * // => true
     *
     * _.isArrayLikeObject('abc');
     * // => false
     *
     * _.isArrayLikeObject(_.noop);
     * // => false
     */
    function isArrayLikeObject(value) {
      return isObjectLike(value) && isArrayLike(value);
    }

    /**
     * Checks if `value` is classified as a boolean primitive or object.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Lang
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is a boolean, else `false`.
     * @example
     *
     * _.isBoolean(false);
     * // => true
     *
     * _.isBoolean(null);
     * // => false
     */
    function isBoolean(value) {
      return value === true || value === false ||
        (isObjectLike(value) && baseGetTag(value) == boolTag);
    }

    /**
     * Checks if `value` is a buffer.
     *
     * @static
     * @memberOf _
     * @since 4.3.0
     * @category Lang
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is a buffer, else `false`.
     * @example
     *
     * _.isBuffer(new Buffer(2));
     * // => true
     *
     * _.isBuffer(new Uint8Array(2));
     * // => false
     */
    var isBuffer = nativeIsBuffer || stubFalse;

    /**
     * Checks if `value` is classified as a `Date` object.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Lang
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is a date object, else `false`.
     * @example
     *
     * _.isDate(new Date);
     * // => true
     *
     * _.isDate('Mon April 23 2012');
     * // => false
     */
    var isDate = nodeIsDate ? baseUnary(nodeIsDate) : baseIsDate;

    /**
     * Checks if `value` is likely a DOM element.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Lang
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is a DOM element, else `false`.
     * @example
     *
     * _.isElement(document.body);
     * // => true
     *
     * _.isElement('<body>');
     * // => false
     */
    function isElement(value) {
      return isObjectLike(value) && value.nodeType === 1 && !isPlainObject(value);
    }

    /**
     * Checks if `value` is an empty object, collection, map, or set.
     *
     * Objects are considered empty if they have no own enumerable string keyed
     * properties.
     *
     * Array-like values such as `arguments` objects, arrays, buffers, strings, or
     * jQuery-like collections are considered empty if they have a `length` of `0`.
     * Similarly, maps and sets are considered empty if they have a `size` of `0`.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Lang
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is empty, else `false`.
     * @example
     *
     * _.isEmpty(null);
     * // => true
     *
     * _.isEmpty(true);
     * // => true
     *
     * _.isEmpty(1);
     * // => true
     *
     * _.isEmpty([1, 2, 3]);
     * // => false
     *
     * _.isEmpty({ 'a': 1 });
     * // => false
     */
    function isEmpty(value) {
      if (value == null) {
        return true;
      }
      if (isArrayLike(value) &&
          (isArray(value) || typeof value == 'string' || typeof value.splice == 'function' ||
            isBuffer(value) || isTypedArray(value) || isArguments(value))) {
        return !value.length;
      }
      var tag = getTag(value);
      if (tag == mapTag || tag == setTag) {
        return !value.size;
      }
      if (isPrototype(value)) {
        return !baseKeys(value).length;
      }
      for (var key in value) {
        if (hasOwnProperty.call(value, key)) {
          return false;
        }
      }
      return true;
    }

    /**
     * Performs a deep comparison between two values to determine if they are
     * equivalent.
     *
     * **Note:** This method supports comparing arrays, array buffers, booleans,
     * date objects, error objects, maps, numbers, `Object` objects, regexes,
     * sets, strings, symbols, and typed arrays. `Object` objects are compared
     * by their own, not inherited, enumerable properties. Functions and DOM
     * nodes are compared by strict equality, i.e. `===`.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Lang
     * @param {*} value The value to compare.
     * @param {*} other The other value to compare.
     * @returns {boolean} Returns `true` if the values are equivalent, else `false`.
     * @example
     *
     * var object = { 'a': 1 };
     * var other = { 'a': 1 };
     *
     * _.isEqual(object, other);
     * // => true
     *
     * object === other;
     * // => false
     */
    function isEqual(value, other) {
      return baseIsEqual(value, other);
    }

    /**
     * This method is like `_.isEqual` except that it accepts `customizer` which
     * is invoked to compare values. If `customizer` returns `undefined`, comparisons
     * are handled by the method instead. The `customizer` is invoked with up to
     * six arguments: (objValue, othValue [, index|key, object, other, stack]).
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Lang
     * @param {*} value The value to compare.
     * @param {*} other The other value to compare.
     * @param {Function} [customizer] The function to customize comparisons.
     * @returns {boolean} Returns `true` if the values are equivalent, else `false`.
     * @example
     *
     * function isGreeting(value) {
     *   return /^h(?:i|ello)$/.test(value);
     * }
     *
     * function customizer(objValue, othValue) {
     *   if (isGreeting(objValue) && isGreeting(othValue)) {
     *     return true;
     *   }
     * }
     *
     * var array = ['hello', 'goodbye'];
     * var other = ['hi', 'goodbye'];
     *
     * _.isEqualWith(array, other, customizer);
     * // => true
     */
    function isEqualWith(value, other, customizer) {
      customizer = typeof customizer == 'function' ? customizer : undefined;
      var result = customizer ? customizer(value, other) : undefined;
      return result === undefined ? baseIsEqual(value, other, undefined, customizer) : !!result;
    }

    /**
     * Checks if `value` is an `Error`, `EvalError`, `RangeError`, `ReferenceError`,
     * `SyntaxError`, `TypeError`, or `URIError` object.
     *
     * @static
     * @memberOf _
     * @since 3.0.0
     * @category Lang
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is an error object, else `false`.
     * @example
     *
     * _.isError(new Error);
     * // => true
     *
     * _.isError(Error);
     * // => false
     */
    function isError(value) {
      if (!isObjectLike(value)) {
        return false;
      }
      var tag = baseGetTag(value);
      return tag == errorTag || tag == domExcTag ||
        (typeof value.message == 'string' && typeof value.name == 'string' && !isPlainObject(value));
    }

    /**
     * Checks if `value` is a finite primitive number.
     *
     * **Note:** This method is based on
     * [`Number.isFinite`](https://mdn.io/Number/isFinite).
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Lang
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is a finite number, else `false`.
     * @example
     *
     * _.isFinite(3);
     * // => true
     *
     * _.isFinite(Number.MIN_VALUE);
     * // => true
     *
     * _.isFinite(Infinity);
     * // => false
     *
     * _.isFinite('3');
     * // => false
     */
    function isFinite(value) {
      return typeof value == 'number' && nativeIsFinite(value);
    }

    /**
     * Checks if `value` is classified as a `Function` object.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Lang
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is a function, else `false`.
     * @example
     *
     * _.isFunction(_);
     * // => true
     *
     * _.isFunction(/abc/);
     * // => false
     */
    function isFunction(value) {
      if (!isObject(value)) {
        return false;
      }
      // The use of `Object#toString` avoids issues with the `typeof` operator
      // in Safari 9 which returns 'object' for typed arrays and other constructors.
      var tag = baseGetTag(value);
      return tag == funcTag || tag == genTag || tag == asyncTag || tag == proxyTag;
    }

    /**
     * Checks if `value` is an integer.
     *
     * **Note:** This method is based on
     * [`Number.isInteger`](https://mdn.io/Number/isInteger).
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Lang
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is an integer, else `false`.
     * @example
     *
     * _.isInteger(3);
     * // => true
     *
     * _.isInteger(Number.MIN_VALUE);
     * // => false
     *
     * _.isInteger(Infinity);
     * // => false
     *
     * _.isInteger('3');
     * // => false
     */
    function isInteger(value) {
      return typeof value == 'number' && value == toInteger(value);
    }

    /**
     * Checks if `value` is a valid array-like length.
     *
     * **Note:** This method is loosely based on
     * [`ToLength`](http://ecma-international.org/ecma-262/7.0/#sec-tolength).
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Lang
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is a valid length, else `false`.
     * @example
     *
     * _.isLength(3);
     * // => true
     *
     * _.isLength(Number.MIN_VALUE);
     * // => false
     *
     * _.isLength(Infinity);
     * // => false
     *
     * _.isLength('3');
     * // => false
     */
    function isLength(value) {
      return typeof value == 'number' &&
        value > -1 && value % 1 == 0 && value <= MAX_SAFE_INTEGER;
    }

    /**
     * Checks if `value` is the
     * [language type](http://www.ecma-international.org/ecma-262/7.0/#sec-ecmascript-language-types)
     * of `Object`. (e.g. arrays, functions, objects, regexes, `new Number(0)`, and `new String('')`)
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Lang
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is an object, else `false`.
     * @example
     *
     * _.isObject({});
     * // => true
     *
     * _.isObject([1, 2, 3]);
     * // => true
     *
     * _.isObject(_.noop);
     * // => true
     *
     * _.isObject(null);
     * // => false
     */
    function isObject(value) {
      var type = typeof value;
      return value != null && (type == 'object' || type == 'function');
    }

    /**
     * Checks if `value` is object-like. A value is object-like if it's not `null`
     * and has a `typeof` result of "object".
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Lang
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is object-like, else `false`.
     * @example
     *
     * _.isObjectLike({});
     * // => true
     *
     * _.isObjectLike([1, 2, 3]);
     * // => true
     *
     * _.isObjectLike(_.noop);
     * // => false
     *
     * _.isObjectLike(null);
     * // => false
     */
    function isObjectLike(value) {
      return value != null && typeof value == 'object';
    }

    /**
     * Checks if `value` is classified as a `Map` object.
     *
     * @static
     * @memberOf _
     * @since 4.3.0
     * @category Lang
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is a map, else `false`.
     * @example
     *
     * _.isMap(new Map);
     * // => true
     *
     * _.isMap(new WeakMap);
     * // => false
     */
    var isMap = nodeIsMap ? baseUnary(nodeIsMap) : baseIsMap;

    /**
     * Performs a partial deep comparison between `object` and `source` to
     * determine if `object` contains equivalent property values.
     *
     * **Note:** This method is equivalent to `_.matches` when `source` is
     * partially applied.
     *
     * Partial comparisons will match empty array and empty object `source`
     * values against any array or object value, respectively. See `_.isEqual`
     * for a list of supported value comparisons.
     *
     * @static
     * @memberOf _
     * @since 3.0.0
     * @category Lang
     * @param {Object} object The object to inspect.
     * @param {Object} source The object of property values to match.
     * @returns {boolean} Returns `true` if `object` is a match, else `false`.
     * @example
     *
     * var object = { 'a': 1, 'b': 2 };
     *
     * _.isMatch(object, { 'b': 2 });
     * // => true
     *
     * _.isMatch(object, { 'b': 1 });
     * // => false
     */
    function isMatch(object, source) {
      return object === source || baseIsMatch(object, source, getMatchData(source));
    }

    /**
     * This method is like `_.isMatch` except that it accepts `customizer` which
     * is invoked to compare values. If `customizer` returns `undefined`, comparisons
     * are handled by the method instead. The `customizer` is invoked with five
     * arguments: (objValue, srcValue, index|key, object, source).
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Lang
     * @param {Object} object The object to inspect.
     * @param {Object} source The object of property values to match.
     * @param {Function} [customizer] The function to customize comparisons.
     * @returns {boolean} Returns `true` if `object` is a match, else `false`.
     * @example
     *
     * function isGreeting(value) {
     *   return /^h(?:i|ello)$/.test(value);
     * }
     *
     * function customizer(objValue, srcValue) {
     *   if (isGreeting(objValue) && isGreeting(srcValue)) {
     *     return true;
     *   }
     * }
     *
     * var object = { 'greeting': 'hello' };
     * var source = { 'greeting': 'hi' };
     *
     * _.isMatchWith(object, source, customizer);
     * // => true
     */
    function isMatchWith(object, source, customizer) {
      customizer = typeof customizer == 'function' ? customizer : undefined;
      return baseIsMatch(object, source, getMatchData(source), customizer);
    }

    /**
     * Checks if `value` is `NaN`.
     *
     * **Note:** This method is based on
     * [`Number.isNaN`](https://mdn.io/Number/isNaN) and is not the same as
     * global [`isNaN`](https://mdn.io/isNaN) which returns `true` for
     * `undefined` and other non-number values.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Lang
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is `NaN`, else `false`.
     * @example
     *
     * _.isNaN(NaN);
     * // => true
     *
     * _.isNaN(new Number(NaN));
     * // => true
     *
     * isNaN(undefined);
     * // => true
     *
     * _.isNaN(undefined);
     * // => false
     */
    function isNaN(value) {
      // An `NaN` primitive is the only value that is not equal to itself.
      // Perform the `toStringTag` check first to avoid errors with some
      // ActiveX objects in IE.
      return isNumber(value) && value != +value;
    }

    /**
     * Checks if `value` is a pristine native function.
     *
     * **Note:** This method can't reliably detect native functions in the presence
     * of the core-js package because core-js circumvents this kind of detection.
     * Despite multiple requests, the core-js maintainer has made it clear: any
     * attempt to fix the detection will be obstructed. As a result, we're left
     * with little choice but to throw an error. Unfortunately, this also affects
     * packages, like [babel-polyfill](https://www.npmjs.com/package/babel-polyfill),
     * which rely on core-js.
     *
     * @static
     * @memberOf _
     * @since 3.0.0
     * @category Lang
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is a native function,
     *  else `false`.
     * @example
     *
     * _.isNative(Array.prototype.push);
     * // => true
     *
     * _.isNative(_);
     * // => false
     */
    function isNative(value) {
      if (isMaskable(value)) {
        throw new Error(CORE_ERROR_TEXT);
      }
      return baseIsNative(value);
    }

    /**
     * Checks if `value` is `null`.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Lang
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is `null`, else `false`.
     * @example
     *
     * _.isNull(null);
     * // => true
     *
     * _.isNull(void 0);
     * // => false
     */
    function isNull(value) {
      return value === null;
    }

    /**
     * Checks if `value` is `null` or `undefined`.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Lang
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is nullish, else `false`.
     * @example
     *
     * _.isNil(null);
     * // => true
     *
     * _.isNil(void 0);
     * // => true
     *
     * _.isNil(NaN);
     * // => false
     */
    function isNil(value) {
      return value == null;
    }

    /**
     * Checks if `value` is classified as a `Number` primitive or object.
     *
     * **Note:** To exclude `Infinity`, `-Infinity`, and `NaN`, which are
     * classified as numbers, use the `_.isFinite` method.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Lang
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is a number, else `false`.
     * @example
     *
     * _.isNumber(3);
     * // => true
     *
     * _.isNumber(Number.MIN_VALUE);
     * // => true
     *
     * _.isNumber(Infinity);
     * // => true
     *
     * _.isNumber('3');
     * // => false
     */
    function isNumber(value) {
      return typeof value == 'number' ||
        (isObjectLike(value) && baseGetTag(value) == numberTag);
    }

    /**
     * Checks if `value` is a plain object, that is, an object created by the
     * `Object` constructor or one with a `[[Prototype]]` of `null`.
     *
     * @static
     * @memberOf _
     * @since 0.8.0
     * @category Lang
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is a plain object, else `false`.
     * @example
     *
     * function Foo() {
     *   this.a = 1;
     * }
     *
     * _.isPlainObject(new Foo);
     * // => false
     *
     * _.isPlainObject([1, 2, 3]);
     * // => false
     *
     * _.isPlainObject({ 'x': 0, 'y': 0 });
     * // => true
     *
     * _.isPlainObject(Object.create(null));
     * // => true
     */
    function isPlainObject(value) {
      if (!isObjectLike(value) || baseGetTag(value) != objectTag) {
        return false;
      }
      var proto = getPrototype(value);
      if (proto === null) {
        return true;
      }
      var Ctor = hasOwnProperty.call(proto, 'constructor') && proto.constructor;
      return typeof Ctor == 'function' && Ctor instanceof Ctor &&
        funcToString.call(Ctor) == objectCtorString;
    }

    /**
     * Checks if `value` is classified as a `RegExp` object.
     *
     * @static
     * @memberOf _
     * @since 0.1.0
     * @category Lang
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is a regexp, else `false`.
     * @example
     *
     * _.isRegExp(/abc/);
     * // => true
     *
     * _.isRegExp('/abc/');
     * // => false
     */
    var isRegExp = nodeIsRegExp ? baseUnary(nodeIsRegExp) : baseIsRegExp;

    /**
     * Checks if `value` is a safe integer. An integer is safe if it's an IEEE-754
     * double precision number which isn't the result of a rounded unsafe integer.
     *
     * **Note:** This method is based on
     * [`Number.isSafeInteger`](https://mdn.io/Number/isSafeInteger).
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Lang
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is a safe integer, else `false`.
     * @example
     *
     * _.isSafeInteger(3);
     * // => true
     *
     * _.isSafeInteger(Number.MIN_VALUE);
     * // => false
     *
     * _.isSafeInteger(Infinity);
     * // => false
     *
     * _.isSafeInteger('3');
     * // => false
     */
    function isSafeInteger(value) {
      return isInteger(value) && value >= -MAX_SAFE_INTEGER && value <= MAX_SAFE_INTEGER;
    }

    /**
     * Checks if `value` is classified as a `Set` object.
     *
     * @static
     * @memberOf _
     * @since 4.3.0
     * @category Lang
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is a set, else `false`.
     * @example
     *
     * _.isSet(new Set);
     * // => true
     *
     * _.isSet(new WeakSet);
     * // => false
     */
    var isSet = nodeIsSet ? baseUnary(nodeIsSet) : baseIsSet;

    /**
     * Checks if `value` is classified as a `String` primitive or object.
     *
     * @static
     * @since 0.1.0
     * @memberOf _
     * @category Lang
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is a string, else `false`.
     * @example
     *
     * _.isString('abc');
     * // => true
     *
     * _.isString(1);
     * // => false
     */
    function isString(value) {
      return typeof value == 'string' ||
        (!isArray(value) && isObjectLike(value) && baseGetTag(value) == stringTag);
    }

    /**
     * Checks if `value` is classified as a `Symbol` primitive or object.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Lang
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is a symbol, else `false`.
     * @example
     *
     * _.isSymbol(Symbol.iterator);
     * // => true
     *
     * _.isSymbol('abc');
     * // => false
     */
    function isSymbol(value) {
      return typeof value == 'symbol' ||
        (isObjectLike(value) && baseGetTag(value) == symbolTag);
    }

    /**
     * Checks if `value` is classified as a typed array.
     *
     * @static
     * @memberOf _
     * @since 3.0.0
     * @category Lang
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is a typed array, else `false`.
     * @example
     *
     * _.isTypedArray(new Uint8Array);
     * // => true
     *
     * _.isTypedArray([]);
     * // => false
     */
    var isTypedArray = nodeIsTypedArray ? baseUnary(nodeIsTypedArray) : baseIsTypedArray;

    /**
     * Checks if `value` is `undefined`.
     *
     * @static
     * @since 0.1.0
     * @memberOf _
     * @category Lang
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is `undefined`, else `false`.
     * @example
     *
     * _.isUndefined(void 0);
     * // => true
     *
     * _.isUndefined(null);
     * // => false
     */
    function isUndefined(value) {
      return value === undefined;
    }

    /**
     * Checks if `value` is classified as a `WeakMap` object.
     *
     * @static
     * @memberOf _
     * @since 4.3.0
     * @category Lang
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is a weak map, else `false`.
     * @example
     *
     * _.isWeakMap(new WeakMap);
     * // => true
     *
     * _.isWeakMap(new Map);
     * // => false
     */
    function isWeakMap(value) {
      return isObjectLike(value) && getTag(value) == weakMapTag;
    }

    /**
     * Checks if `value` is classified as a `WeakSet` object.
     *
     * @static
     * @memberOf _
     * @since 4.3.0
     * @category Lang
     * @param {*} value The value to check.
     * @returns {boolean} Returns `true` if `value` is a weak set, else `false`.
     * @example
     *
     * _.isWeakSet(new WeakSet);
     * // => true
     *
     * _.isWeakSet(new Set);
     * // => false
     */
    function isWeakSet(value) {
      return isObjectLike(value) && baseGetTag(value) == weakSetTag;
    }

    /**
     * Checks if `value` is less than `other`.
     *
     * @static
     * @memberOf _
     * @since 3.9.0
     * @category Lang
     * @param {*} value The value to compare.
     * @param {*} other The other value to compare.
     * @returns {boolean} Returns `true` if `value` is less than `other`,
     *  else `false`.
     * @see _.gt
     * @example
     *
     * _.lt(1, 3);
     * // => true
     *
     * _.lt(3, 3);
     * // => false
     *
     * _.lt(3, 1);
     * // => false
     */
    var lt = createRelationalOperation(baseLt);

    /**
     * Checks if `value` is less than or equal to `other`.
     *
     * @static
     * @memberOf _
     * @since 3.9.0
     * @category Lang
     * @param {*} value The value to compare.
     * @param {*} other The other value to compare.
     * @returns {boolean} Returns `true` if `value` is less than or equal to
     *  `other`, else `false`.
     * @see _.gte
     * @example
     *
     * _.lte(1, 3);
     * // => true
     *
     * _.lte(3, 3);
     * // => true
     *
     * _.lte(3, 1);
     * // => false
     */
    var lte = createRelationalOperation(function(value, other) {
      return value <= other;
    });

    /**
     * Converts `value` to an array.
     *
     * @static
     * @since 0.1.0
     * @memberOf _
     * @category Lang
     * @param {*} value The value to convert.
     * @returns {Array} Returns the converted array.
     * @example
     *
     * _.toArray({ 'a': 1, 'b': 2 });
     * // => [1, 2]
     *
     * _.toArray('abc');
     * // => ['a', 'b', 'c']
     *
     * _.toArray(1);
     * // => []
     *
     * _.toArray(null);
     * // => []
     */
    function toArray(value) {
      if (!value) {
        return [];
      }
      if (isArrayLike(value)) {
        return isString(value) ? stringToArray(value) : copyArray(value);
      }
      if (symIterator && value[symIterator]) {
        return iteratorToArray(value[symIterator]());
      }
      var tag = getTag(value),
          func = tag == mapTag ? mapToArray : (tag == setTag ? setToArray : values);

      return func(value);
    }

    /**
     * Converts `value` to a finite number.
     *
     * @static
     * @memberOf _
     * @since 4.12.0
     * @category Lang
     * @param {*} value The value to convert.
     * @returns {number} Returns the converted number.
     * @example
     *
     * _.toFinite(3.2);
     * // => 3.2
     *
     * _.toFinite(Number.MIN_VALUE);
     * // => 5e-324
     *
     * _.toFinite(Infinity);
     * // => 1.7976931348623157e+308
     *
     * _.toFinite('3.2');
     * // => 3.2
     */
    function toFinite(value) {
      if (!value) {
        return value === 0 ? value : 0;
      }
      value = toNumber(value);
      if (value === INFINITY || value === -INFINITY) {
        var sign = (value < 0 ? -1 : 1);
        return sign * MAX_INTEGER;
      }
      return value === value ? value : 0;
    }

    /**
     * Converts `value` to an integer.
     *
     * **Note:** This method is loosely based on
     * [`ToInteger`](http://www.ecma-international.org/ecma-262/7.0/#sec-tointeger).
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Lang
     * @param {*} value The value to convert.
     * @returns {number} Returns the converted integer.
     * @example
     *
     * _.toInteger(3.2);
     * // => 3
     *
     * _.toInteger(Number.MIN_VALUE);
     * // => 0
     *
     * _.toInteger(Infinity);
     * // => 1.7976931348623157e+308
     *
     * _.toInteger('3.2');
     * // => 3
     */
    function toInteger(value) {
      var result = toFinite(value),
          remainder = result % 1;

      return result === result ? (remainder ? result - remainder : result) : 0;
    }

    /**
     * Converts `value` to an integer suitable for use as the length of an
     * array-like object.
     *
     * **Note:** This method is based on
     * [`ToLength`](http://ecma-international.org/ecma-262/7.0/#sec-tolength).
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Lang
     * @param {*} value The value to convert.
     * @returns {number} Returns the converted integer.
     * @example
     *
     * _.toLength(3.2);
     * // => 3
     *
     * _.toLength(Number.MIN_VALUE);
     * // => 0
     *
     * _.toLength(Infinity);
     * // => 4294967295
     *
     * _.toLength('3.2');
     * // => 3
     */
    function toLength(value) {
      return value ? baseClamp(toInteger(value), 0, MAX_ARRAY_LENGTH) : 0;
    }

    /**
     * Converts `value` to a number.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Lang
     * @param {*} value The value to process.
     * @returns {number} Returns the number.
     * @example
     *
     * _.toNumber(3.2);
     * // => 3.2
     *
     * _.toNumber(Number.MIN_VALUE);
     * // => 5e-324
     *
     * _.toNumber(Infinity);
     * // => Infinity
     *
     * _.toNumber('3.2');
     * // => 3.2
     */
    function toNumber(value) {
      if (typeof value == 'number') {
        return value;
      }
      if (isSymbol(value)) {
        return NAN;
      }
      if (isObject(value)) {
        var other = typeof value.valueOf == 'function' ? value.valueOf() : value;
        value = isObject(other) ? (other + '') : other;
      }
      if (typeof value != 'string') {
        return value === 0 ? value : +value;
      }
      value = baseTrim(value);
      var isBinary = reIsBinary.test(value);
      return (isBinary || reIsOctal.test(value))
        ? freeParseInt(value.slice(2), isBinary ? 2 : 8)
        : (reIsBadHex.test(value) ? NAN : +value);
    }

    /**
     * Converts `value` to a plain object flattening inherited enumerable string
     * keyed properties of `value` to own properties of the plain object.
     *
     * @static
     * @memberOf _
     * @since 3.0.0
     * @category Lang
     * @param {*} value The value to convert.
     * @returns {Object} Returns the converted plain object.
     * @example
     *
     * function Foo() {
     *   this.b = 2;
     * }
     *
     * Foo.prototype.c = 3;
     *
     * _.assign({ 'a': 1 }, new Foo);
     * // => { 'a': 1, 'b': 2 }
     *
     * _.assign({ 'a': 1 }, _.toPlainObject(new Foo));
     * // => { 'a': 1, 'b': 2, 'c': 3 }
     */
    function toPlainObject(value) {
      return copyObject(value, keysIn(value));
    }

    /**
     * Converts `value` to a safe integer. A safe integer can be compared and
     * represented correctly.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Lang
     * @param {*} value The value to convert.
     * @returns {number} Returns the converted integer.
     * @example
     *
     * _.toSafeInteger(3.2);
     * // => 3
     *
     * _.toSafeInteger(Number.MIN_VALUE);
     * // => 0
     *
     * _.toSafeInteger(Infinity);
     * // => 9007199254740991
     *
     * _.toSafeInteger('3.2');
     * // => 3
     */
    function toSafeInteger(value) {
      return value
        ? baseClamp(toInteger(value), -MAX_SAFE_INTEGER, MAX_SAFE_INTEGER)
        : (value === 0 ? value : 0);
    }

    /**
     * Converts `value` to a string. An empty string is returned for `null`
     * and `undefined` values. The sign of `-0` is preserved.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Lang
     * @param {*} value The value to convert.
     * @returns {string} Returns the converted string.
     * @example
     *
     * _.toString(null);
     * // => ''
     *
     * _.toString(-0);
     * // => '-0'
     *
     * _.toString([1, 2, 3]);
     * // => '1,2,3'
     */
    function toString(value) {
      return value == null ? '' : baseToString(value);
    }

    /*------------------------------------------------------------------------*/

    /**
     * Assigns own enumerable string keyed properties of source objects to the
     * destination object. Source objects are applied from left to right.
     * Subsequent sources overwrite property assignments of previous sources.
     *
     * **Note:** This method mutates `object` and is loosely based on
     * [`Object.assign`](https://mdn.io/Object/assign).
     *
     * @static
     * @memberOf _
     * @since 0.10.0
     * @category Object
     * @param {Object} object The destination object.
     * @param {...Object} [sources] The source objects.
     * @returns {Object} Returns `object`.
     * @see _.assignIn
     * @example
     *
     * function Foo() {
     *   this.a = 1;
     * }
     *
     * function Bar() {
     *   this.c = 3;
     * }
     *
     * Foo.prototype.b = 2;
     * Bar.prototype.d = 4;
     *
     * _.assign({ 'a': 0 }, new Foo, new Bar);
     * // => { 'a': 1, 'c': 3 }
     */
    var assign = createAssigner(function(object, source) {
      if (isPrototype(source) || isArrayLike(source)) {
        copyObject(source, keys(source), object);
        return;
      }
      for (var key in source) {
        if (hasOwnProperty.call(source, key)) {
          assignValue(object, key, source[key]);
        }
      }
    });

    /**
     * This method is like `_.assign` except that it iterates over own and
     * inherited source properties.
     *
     * **Note:** This method mutates `object`.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @alias extend
     * @category Object
     * @param {Object} object The destination object.
     * @param {...Object} [sources] The source objects.
     * @returns {Object} Returns `object`.
     * @see _.assign
     * @example
     *
     * function Foo() {
     *   this.a = 1;
     * }
     *
     * function Bar() {
     *   this.c = 3;
     * }
     *
     * Foo.prototype.b = 2;
     * Bar.prototype.d = 4;
     *
     * _.assignIn({ 'a': 0 }, new Foo, new Bar);
     * // => { 'a': 1, 'b': 2, 'c': 3, 'd': 4 }
     */
    var assignIn = createAssigner(function(object, source) {
      copyObject(source, keysIn(source), object);
    });

    /**
     * This method is like `_.assignIn` except that it accepts `customizer`
     * which is invoked to produce the assigned values. If `customizer` returns
     * `undefined`, assignment is handled by the method instead. The `customizer`
     * is invoked with five arguments: (objValue, srcValue, key, object, source).
     *
     * **Note:** This method mutates `object`.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @alias extendWith
     * @category Object
     * @param {Object} object The destination object.
     * @param {...Object} sources The source objects.
     * @param {Function} [customizer] The function to customize assigned values.
     * @returns {Object} Returns `object`.
     * @see _.assignWith
     * @example
     *
     * function customizer(objValue, srcValue) {
     *   return _.isUndefined(objValue) ? srcValue : objValue;
     * }
     *
     * var defaults = _.partialRight(_.assignInWith, customizer);
     *
     * defaults({ 'a': 1 }, { 'b': 2 }, { 'a': 3 });
     * // => { 'a': 1, 'b': 2 }
     */
    var assignInWith = createAssigner(function(object, source, srcIndex, customizer) {
      copyObject(source, keysIn(source), object, customizer);
    });

    /**
     * This method is like `_.assign` except that it accepts `customizer`
     * which is invoked to produce the assigned values. If `customizer` returns
     * `undefined`, assignment is handled by the method instead. The `customizer`
     * is invoked with five arguments: (objValue, srcValue, key, object, source).
     *
     * **Note:** This method mutates `object`.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Object
     * @param {Object} object The destination object.
     * @param {...Object} sources The source objects.
     * @param {Function} [customizer] The function to customize assigned values.
     * @returns {Object} Returns `object`.
     * @see _.assignInWith
     * @example
     *
     * function customizer(objValue, srcValue) {
     *   return _.isUndefined(objValue) ? srcValue : objValue;
     * }
     *
     * var defaults = _.partialRight(_.assignWith, customizer);
     *
     * defaults({ 'a': 1 }, { 'b': 2 }, { 'a': 3 });
     * // => { 'a': 1, 'b': 2 }
     */
    var assignWith = createAssigner(function(object, source, srcIndex, customizer) {
      copyObject(source, keys(source), object, customizer);
    });

    /**
     * Creates an array of values corresponding to `paths` of `object`.
     *
     * @static
     * @memberOf _
     * @since 1.0.0
     * @category Object
     * @param {Object} object The object to iterate over.
     * @param {...(string|string[])} [paths] The property paths to pick.
     * @returns {Array} Returns the picked values.
     * @example
     *
     * var object = { 'a': [{ 'b': { 'c': 3 } }, 4] };
     *
     * _.at(object, ['a[0].b.c', 'a[1]']);
     * // => [3, 4]
     */
    var at = flatRest(baseAt);

    /**
     * Creates an object that inherits from the `prototype` object. If a
     * `properties` object is given, its own enumerable string keyed properties
     * are assigned to the created object.
     *
     * @static
     * @memberOf _
     * @since 2.3.0
     * @category Object
     * @param {Object} prototype The object to inherit from.
     * @param {Object} [properties] The properties to assign to the object.
     * @returns {Object} Returns the new object.
     * @example
     *
     * function Shape() {
     *   this.x = 0;
     *   this.y = 0;
     * }
     *
     * function Circle() {
     *   Shape.call(this);
     * }
     *
     * Circle.prototype = _.create(Shape.prototype, {
     *   'constructor': Circle
     * });
     *
     * var circle = new Circle;
     * circle instanceof Circle;
     * // => true
     *
     * circle instanceof Shape;
     * // => true
     */
    function create(prototype, properties) {
      var result = baseCreate(prototype);
      return properties == null ? result : baseAssign(result, properties);
    }

    /**
     * Assigns own and inherited enumerable string keyed properties of source
     * objects to the destination object for all destination properties that
     * resolve to `undefined`. Source objects are applied from left to right.
     * Once a property is set, additional values of the same property are ignored.
     *
     * **Note:** This method mutates `object`.
     *
     * @static
     * @since 0.1.0
     * @memberOf _
     * @category Object
     * @param {Object} object The destination object.
     * @param {...Object} [sources] The source objects.
     * @returns {Object} Returns `object`.
     * @see _.defaultsDeep
     * @example
     *
     * _.defaults({ 'a': 1 }, { 'b': 2 }, { 'a': 3 });
     * // => { 'a': 1, 'b': 2 }
     */
    var defaults = baseRest(function(object, sources) {
      object = Object(object);

      var index = -1;
      var length = sources.length;
      var guard = length > 2 ? sources[2] : undefined;

      if (guard && isIterateeCall(sources[0], sources[1], guard)) {
        length = 1;
      }

      while (++index < length) {
        var source = sources[index];
        var props = keysIn(source);
        var propsIndex = -1;
        var propsLength = props.length;

        while (++propsIndex < propsLength) {
          var key = props[propsIndex];
          var value = object[key];

          if (value === undefined ||
              (eq(value, objectProto[key]) && !hasOwnProperty.call(object, key))) {
            object[key] = source[key];
          }
        }
      }

      return object;
    });

    /**
     * This method is like `_.defaults` except that it recursively assigns
     * default properties.
     *
     * **Note:** This method mutates `object`.
     *
     * @static
     * @memberOf _
     * @since 3.10.0
     * @category Object
     * @param {Object} object The destination object.
     * @param {...Object} [sources] The source objects.
     * @returns {Object} Returns `object`.
     * @see _.defaults
     * @example
     *
     * _.defaultsDeep({ 'a': { 'b': 2 } }, { 'a': { 'b': 1, 'c': 3 } });
     * // => { 'a': { 'b': 2, 'c': 3 } }
     */
    var defaultsDeep = baseRest(function(args) {
      args.push(undefined, customDefaultsMerge);
      return apply(mergeWith, undefined, args);
    });

    /**
     * This method is like `_.find` except that it returns the key of the first
     * element `predicate` returns truthy for instead of the element itself.
     *
     * @static
     * @memberOf _
     * @since 1.1.0
     * @category Object
     * @param {Object} object The object to inspect.
     * @param {Function} [predicate=_.identity] The function invoked per iteration.
     * @returns {string|undefined} Returns the key of the matched element,
     *  else `undefined`.
     * @example
     *
     * var users = {
     *   'barney':  { 'age': 36, 'active': true },
     *   'fred':    { 'age': 40, 'active': false },
     *   'pebbles': { 'age': 1,  'active': true }
     * };
     *
     * _.findKey(users, function(o) { return o.age < 40; });
     * // => 'barney' (iteration order is not guaranteed)
     *
     * // The `_.matches` iteratee shorthand.
     * _.findKey(users, { 'age': 1, 'active': true });
     * // => 'pebbles'
     *
     * // The `_.matchesProperty` iteratee shorthand.
     * _.findKey(users, ['active', false]);
     * // => 'fred'
     *
     * // The `_.property` iteratee shorthand.
     * _.findKey(users, 'active');
     * // => 'barney'
     */
    function findKey(object, predicate) {
      return baseFindKey(object, getIteratee(predicate, 3), baseForOwn);
    }

    /**
     * This method is like `_.findKey` except that it iterates over elements of
     * a collection in the opposite order.
     *
     * @static
     * @memberOf _
     * @since 2.0.0
     * @category Object
     * @param {Object} object The object to inspect.
     * @param {Function} [predicate=_.identity] The function invoked per iteration.
     * @returns {string|undefined} Returns the key of the matched element,
     *  else `undefined`.
     * @example
     *
     * var users = {
     *   'barney':  { 'age': 36, 'active': true },
     *   'fred':    { 'age': 40, 'active': false },
     *   'pebbles': { 'age': 1,  'active': true }
     * };
     *
     * _.findLastKey(users, function(o) { return o.age < 40; });
     * // => returns 'pebbles' assuming `_.findKey` returns 'barney'
     *
     * // The `_.matches` iteratee shorthand.
     * _.findLastKey(users, { 'age': 36, 'active': true });
     * // => 'barney'
     *
     * // The `_.matchesProperty` iteratee shorthand.
     * _.findLastKey(users, ['active', false]);
     * // => 'fred'
     *
     * // The `_.property` iteratee shorthand.
     * _.findLastKey(users, 'active');
     * // => 'pebbles'
     */
    function findLastKey(object, predicate) {
      return baseFindKey(object, getIteratee(predicate, 3), baseForOwnRight);
    }

    /**
     * Iterates over own and inherited enumerable string keyed properties of an
     * object and invokes `iteratee` for each property. The iteratee is invoked
     * with three arguments: (value, key, object). Iteratee functions may exit
     * iteration early by explicitly returning `false`.
     *
     * @static
     * @memberOf _
     * @since 0.3.0
     * @category Object
     * @param {Object} object The object to iterate over.
     * @param {Function} [iteratee=_.identity] The function invoked per iteration.
     * @returns {Object} Returns `object`.
     * @see _.forInRight
     * @example
     *
     * function Foo() {
     *   this.a = 1;
     *   this.b = 2;
     * }
     *
     * Foo.prototype.c = 3;
     *
     * _.forIn(new Foo, function(value, key) {
     *   console.log(key);
     * });
     * // => Logs 'a', 'b', then 'c' (iteration order is not guaranteed).
     */
    function forIn(object, iteratee) {
      return object == null
        ? object
        : baseFor(object, getIteratee(iteratee, 3), keysIn);
    }

    /**
     * This method is like `_.forIn` except that it iterates over properties of
     * `object` in the opposite order.
     *
     * @static
     * @memberOf _
     * @since 2.0.0
     * @category Object
     * @param {Object} object The object to iterate over.
     * @param {Function} [iteratee=_.identity] The function invoked per iteration.
     * @returns {Object} Returns `object`.
     * @see _.forIn
     * @example
     *
     * function Foo() {
     *   this.a = 1;
     *   this.b = 2;
     * }
     *
     * Foo.prototype.c = 3;
     *
     * _.forInRight(new Foo, function(value, key) {
     *   console.log(key);
     * });
     * // => Logs 'c', 'b', then 'a' assuming `_.forIn` logs 'a', 'b', then 'c'.
     */
    function forInRight(object, iteratee) {
      return object == null
        ? object
        : baseForRight(object, getIteratee(iteratee, 3), keysIn);
    }

    /**
     * Iterates over own enumerable string keyed properties of an object and
     * invokes `iteratee` for each property. The iteratee is invoked with three
     * arguments: (value, key, object). Iteratee functions may exit iteration
     * early by explicitly returning `false`.
     *
     * @static
     * @memberOf _
     * @since 0.3.0
     * @category Object
     * @param {Object} object The object to iterate over.
     * @param {Function} [iteratee=_.identity] The function invoked per iteration.
     * @returns {Object} Returns `object`.
     * @see _.forOwnRight
     * @example
     *
     * function Foo() {
     *   this.a = 1;
     *   this.b = 2;
     * }
     *
     * Foo.prototype.c = 3;
     *
     * _.forOwn(new Foo, function(value, key) {
     *   console.log(key);
     * });
     * // => Logs 'a' then 'b' (iteration order is not guaranteed).
     */
    function forOwn(object, iteratee) {
      return object && baseForOwn(object, getIteratee(iteratee, 3));
    }

    /**
     * This method is like `_.forOwn` except that it iterates over properties of
     * `object` in the opposite order.
     *
     * @static
     * @memberOf _
     * @since 2.0.0
     * @category Object
     * @param {Object} object The object to iterate over.
     * @param {Function} [iteratee=_.identity] The function invoked per iteration.
     * @returns {Object} Returns `object`.
     * @see _.forOwn
     * @example
     *
     * function Foo() {
     *   this.a = 1;
     *   this.b = 2;
     * }
     *
     * Foo.prototype.c = 3;
     *
     * _.forOwnRight(new Foo, function(value, key) {
     *   console.log(key);
     * });
     * // => Logs 'b' then 'a' assuming `_.forOwn` logs 'a' then 'b'.
     */
    function forOwnRight(object, iteratee) {
      return object && baseForOwnRight(object, getIteratee(iteratee, 3));
    }

    /**
     * Creates an array of function property names from own enumerable properties
     * of `object`.
     *
     * @static
     * @since 0.1.0
     * @memberOf _
     * @category Object
     * @param {Object} object The object to inspect.
     * @returns {Array} Returns the function names.
     * @see _.functionsIn
     * @example
     *
     * function Foo() {
     *   this.a = _.constant('a');
     *   this.b = _.constant('b');
     * }
     *
     * Foo.prototype.c = _.constant('c');
     *
     * _.functions(new Foo);
     * // => ['a', 'b']
     */
    function functions(object) {
      return object == null ? [] : baseFunctions(object, keys(object));
    }

    /**
     * Creates an array of function property names from own and inherited
     * enumerable properties of `object`.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Object
     * @param {Object} object The object to inspect.
     * @returns {Array} Returns the function names.
     * @see _.functions
     * @example
     *
     * function Foo() {
     *   this.a = _.constant('a');
     *   this.b = _.constant('b');
     * }
     *
     * Foo.prototype.c = _.constant('c');
     *
     * _.functionsIn(new Foo);
     * // => ['a', 'b', 'c']
     */
    function functionsIn(object) {
      return object == null ? [] : baseFunctions(object, keysIn(object));
    }

    /**
     * Gets the value at `path` of `object`. If the resolved value is
     * `undefined`, the `defaultValue` is returned in its place.
     *
     * @static
     * @memberOf _
     * @since 3.7.0
     * @category Object
     * @param {Object} object The object to query.
     * @param {Array|string} path The path of the property to get.
     * @param {*} [defaultValue] The value returned for `undefined` resolved values.
     * @returns {*} Returns the resolved value.
     * @example
     *
     * var object = { 'a': [{ 'b': { 'c': 3 } }] };
     *
     * _.get(object, 'a[0].b.c');
     * // => 3
     *
     * _.get(object, ['a', '0', 'b', 'c']);
     * // => 3
     *
     * _.get(object, 'a.b.c', 'default');
     * // => 'default'
     */
    function get(object, path, defaultValue) {
      var result = object == null ? undefined : baseGet(object, path);
      return result === undefined ? defaultValue : result;
    }

    /**
     * Checks if `path` is a direct property of `object`.
     *
     * @static
     * @since 0.1.0
     * @memberOf _
     * @category Object
     * @param {Object} object The object to query.
     * @param {Array|string} path The path to check.
     * @returns {boolean} Returns `true` if `path` exists, else `false`.
     * @example
     *
     * var object = { 'a': { 'b': 2 } };
     * var other = _.create({ 'a': _.create({ 'b': 2 }) });
     *
     * _.has(object, 'a');
     * // => true
     *
     * _.has(object, 'a.b');
     * // => true
     *
     * _.has(object, ['a', 'b']);
     * // => true
     *
     * _.has(other, 'a');
     * // => false
     */
    function has(object, path) {
      return object != null && hasPath(object, path, baseHas);
    }

    /**
     * Checks if `path` is a direct or inherited property of `object`.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Object
     * @param {Object} object The object to query.
     * @param {Array|string} path The path to check.
     * @returns {boolean} Returns `true` if `path` exists, else `false`.
     * @example
     *
     * var object = _.create({ 'a': _.create({ 'b': 2 }) });
     *
     * _.hasIn(object, 'a');
     * // => true
     *
     * _.hasIn(object, 'a.b');
     * // => true
     *
     * _.hasIn(object, ['a', 'b']);
     * // => true
     *
     * _.hasIn(object, 'b');
     * // => false
     */
    function hasIn(object, path) {
      return object != null && hasPath(object, path, baseHasIn);
    }

    /**
     * Creates an object composed of the inverted keys and values of `object`.
     * If `object` contains duplicate values, subsequent values overwrite
     * property assignments of previous values.
     *
     * @static
     * @memberOf _
     * @since 0.7.0
     * @category Object
     * @param {Object} object The object to invert.
     * @returns {Object} Returns the new inverted object.
     * @example
     *
     * var object = { 'a': 1, 'b': 2, 'c': 1 };
     *
     * _.invert(object);
     * // => { '1': 'c', '2': 'b' }
     */
    var invert = createInverter(function(result, value, key) {
      if (value != null &&
          typeof value.toString != 'function') {
        value = nativeObjectToString.call(value);
      }

      result[value] = key;
    }, constant(identity));

    /**
     * This method is like `_.invert` except that the inverted object is generated
     * from the results of running each element of `object` thru `iteratee`. The
     * corresponding inverted value of each inverted key is an array of keys
     * responsible for generating the inverted value. The iteratee is invoked
     * with one argument: (value).
     *
     * @static
     * @memberOf _
     * @since 4.1.0
     * @category Object
     * @param {Object} object The object to invert.
     * @param {Function} [iteratee=_.identity] The iteratee invoked per element.
     * @returns {Object} Returns the new inverted object.
     * @example
     *
     * var object = { 'a': 1, 'b': 2, 'c': 1 };
     *
     * _.invertBy(object);
     * // => { '1': ['a', 'c'], '2': ['b'] }
     *
     * _.invertBy(object, function(value) {
     *   return 'group' + value;
     * });
     * // => { 'group1': ['a', 'c'], 'group2': ['b'] }
     */
    var invertBy = createInverter(function(result, value, key) {
      if (value != null &&
          typeof value.toString != 'function') {
        value = nativeObjectToString.call(value);
      }

      if (hasOwnProperty.call(result, value)) {
        result[value].push(key);
      } else {
        result[value] = [key];
      }
    }, getIteratee);

    /**
     * Invokes the method at `path` of `object`.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Object
     * @param {Object} object The object to query.
     * @param {Array|string} path The path of the method to invoke.
     * @param {...*} [args] The arguments to invoke the method with.
     * @returns {*} Returns the result of the invoked method.
     * @example
     *
     * var object = { 'a': [{ 'b': { 'c': [1, 2, 3, 4] } }] };
     *
     * _.invoke(object, 'a[0].b.c.slice', 1, 3);
     * // => [2, 3]
     */
    var invoke = baseRest(baseInvoke);

    /**
     * Creates an array of the own enumerable property names of `object`.
     *
     * **Note:** Non-object values are coerced to objects. See the
     * [ES spec](http://ecma-international.org/ecma-262/7.0/#sec-object.keys)
     * for more details.
     *
     * @static
     * @since 0.1.0
     * @memberOf _
     * @category Object
     * @param {Object} object The object to query.
     * @returns {Array} Returns the array of property names.
     * @example
     *
     * function Foo() {
     *   this.a = 1;
     *   this.b = 2;
     * }
     *
     * Foo.prototype.c = 3;
     *
     * _.keys(new Foo);
     * // => ['a', 'b'] (iteration order is not guaranteed)
     *
     * _.keys('hi');
     * // => ['0', '1']
     */
    function keys(object) {
      return isArrayLike(object) ? arrayLikeKeys(object) : baseKeys(object);
    }

    /**
     * Creates an array of the own and inherited enumerable property names of `object`.
     *
     * **Note:** Non-object values are coerced to objects.
     *
     * @static
     * @memberOf _
     * @since 3.0.0
     * @category Object
     * @param {Object} object The object to query.
     * @returns {Array} Returns the array of property names.
     * @example
     *
     * function Foo() {
     *   this.a = 1;
     *   this.b = 2;
     * }
     *
     * Foo.prototype.c = 3;
     *
     * _.keysIn(new Foo);
     * // => ['a', 'b', 'c'] (iteration order is not guaranteed)
     */
    function keysIn(object) {
      return isArrayLike(object) ? arrayLikeKeys(object, true) : baseKeysIn(object);
    }

    /**
     * The opposite of `_.mapValues`; this method creates an object with the
     * same values as `object` and keys generated by running each own enumerable
     * string keyed property of `object` thru `iteratee`. The iteratee is invoked
     * with three arguments: (value, key, object).
     *
     * @static
     * @memberOf _
     * @since 3.8.0
     * @category Object
     * @param {Object} object The object to iterate over.
     * @param {Function} [iteratee=_.identity] The function invoked per iteration.
     * @returns {Object} Returns the new mapped object.
     * @see _.mapValues
     * @example
     *
     * _.mapKeys({ 'a': 1, 'b': 2 }, function(value, key) {
     *   return key + value;
     * });
     * // => { 'a1': 1, 'b2': 2 }
     */
    function mapKeys(object, iteratee) {
      var result = {};
      iteratee = getIteratee(iteratee, 3);

      baseForOwn(object, function(value, key, object) {
        baseAssignValue(result, iteratee(value, key, object), value);
      });
      return result;
    }

    /**
     * Creates an object with the same keys as `object` and values generated
     * by running each own enumerable string keyed property of `object` thru
     * `iteratee`. The iteratee is invoked with three arguments:
     * (value, key, object).
     *
     * @static
     * @memberOf _
     * @since 2.4.0
     * @category Object
     * @param {Object} object The object to iterate over.
     * @param {Function} [iteratee=_.identity] The function invoked per iteration.
     * @returns {Object} Returns the new mapped object.
     * @see _.mapKeys
     * @example
     *
     * var users = {
     *   'fred':    { 'user': 'fred',    'age': 40 },
     *   'pebbles': { 'user': 'pebbles', 'age': 1 }
     * };
     *
     * _.mapValues(users, function(o) { return o.age; });
     * // => { 'fred': 40, 'pebbles': 1 } (iteration order is not guaranteed)
     *
     * // The `_.property` iteratee shorthand.
     * _.mapValues(users, 'age');
     * // => { 'fred': 40, 'pebbles': 1 } (iteration order is not guaranteed)
     */
    function mapValues(object, iteratee) {
      var result = {};
      iteratee = getIteratee(iteratee, 3);

      baseForOwn(object, function(value, key, object) {
        baseAssignValue(result, key, iteratee(value, key, object));
      });
      return result;
    }

    /**
     * This method is like `_.assign` except that it recursively merges own and
     * inherited enumerable string keyed properties of source objects into the
     * destination object. Source properties that resolve to `undefined` are
     * skipped if a destination value exists. Array and plain object properties
     * are merged recursively. Other objects and value types are overridden by
     * assignment. Source objects are applied from left to right. Subsequent
     * sources overwrite property assignments of previous sources.
     *
     * **Note:** This method mutates `object`.
     *
     * @static
     * @memberOf _
     * @since 0.5.0
     * @category Object
     * @param {Object} object The destination object.
     * @param {...Object} [sources] The source objects.
     * @returns {Object} Returns `object`.
     * @example
     *
     * var object = {
     *   'a': [{ 'b': 2 }, { 'd': 4 }]
     * };
     *
     * var other = {
     *   'a': [{ 'c': 3 }, { 'e': 5 }]
     * };
     *
     * _.merge(object, other);
     * // => { 'a': [{ 'b': 2, 'c': 3 }, { 'd': 4, 'e': 5 }] }
     */
    var merge = createAssigner(function(object, source, srcIndex) {
      baseMerge(object, source, srcIndex);
    });

    /**
     * This method is like `_.merge` except that it accepts `customizer` which
     * is invoked to produce the merged values of the destination and source
     * properties. If `customizer` returns `undefined`, merging is handled by the
     * method instead. The `customizer` is invoked with six arguments:
     * (objValue, srcValue, key, object, source, stack).
     *
     * **Note:** This method mutates `object`.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Object
     * @param {Object} object The destination object.
     * @param {...Object} sources The source objects.
     * @param {Function} customizer The function to customize assigned values.
     * @returns {Object} Returns `object`.
     * @example
     *
     * function customizer(objValue, srcValue) {
     *   if (_.isArray(objValue)) {
     *     return objValue.concat(srcValue);
     *   }
     * }
     *
     * var object = { 'a': [1], 'b': [2] };
     * var other = { 'a': [3], 'b': [4] };
     *
     * _.mergeWith(object, other, customizer);
     * // => { 'a': [1, 3], 'b': [2, 4] }
     */
    var mergeWith = createAssigner(function(object, source, srcIndex, customizer) {
      baseMerge(object, source, srcIndex, customizer);
    });

    /**
     * The opposite of `_.pick`; this method creates an object composed of the
     * own and inherited enumerable property paths of `object` that are not omitted.
     *
     * **Note:** This method is considerably slower than `_.pick`.
     *
     * @static
     * @since 0.1.0
     * @memberOf _
     * @category Object
     * @param {Object} object The source object.
     * @param {...(string|string[])} [paths] The property paths to omit.
     * @returns {Object} Returns the new object.
     * @example
     *
     * var object = { 'a': 1, 'b': '2', 'c': 3 };
     *
     * _.omit(object, ['a', 'c']);
     * // => { 'b': '2' }
     */
    var omit = flatRest(function(object, paths) {
      var result = {};
      if (object == null) {
        return result;
      }
      var isDeep = false;
      paths = arrayMap(paths, function(path) {
        path = castPath(path, object);
        isDeep || (isDeep = path.length > 1);
        return path;
      });
      copyObject(object, getAllKeysIn(object), result);
      if (isDeep) {
        result = baseClone(result, CLONE_DEEP_FLAG | CLONE_FLAT_FLAG | CLONE_SYMBOLS_FLAG, customOmitClone);
      }
      var length = paths.length;
      while (length--) {
        baseUnset(result, paths[length]);
      }
      return result;
    });

    /**
     * The opposite of `_.pickBy`; this method creates an object composed of
     * the own and inherited enumerable string keyed properties of `object` that
     * `predicate` doesn't return truthy for. The predicate is invoked with two
     * arguments: (value, key).
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Object
     * @param {Object} object The source object.
     * @param {Function} [predicate=_.identity] The function invoked per property.
     * @returns {Object} Returns the new object.
     * @example
     *
     * var object = { 'a': 1, 'b': '2', 'c': 3 };
     *
     * _.omitBy(object, _.isNumber);
     * // => { 'b': '2' }
     */
    function omitBy(object, predicate) {
      return pickBy(object, negate(getIteratee(predicate)));
    }

    /**
     * Creates an object composed of the picked `object` properties.
     *
     * @static
     * @since 0.1.0
     * @memberOf _
     * @category Object
     * @param {Object} object The source object.
     * @param {...(string|string[])} [paths] The property paths to pick.
     * @returns {Object} Returns the new object.
     * @example
     *
     * var object = { 'a': 1, 'b': '2', 'c': 3 };
     *
     * _.pick(object, ['a', 'c']);
     * // => { 'a': 1, 'c': 3 }
     */
    var pick = flatRest(function(object, paths) {
      return object == null ? {} : basePick(object, paths);
    });

    /**
     * Creates an object composed of the `object` properties `predicate` returns
     * truthy for. The predicate is invoked with two arguments: (value, key).
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Object
     * @param {Object} object The source object.
     * @param {Function} [predicate=_.identity] The function invoked per property.
     * @returns {Object} Returns the new object.
     * @example
     *
     * var object = { 'a': 1, 'b': '2', 'c': 3 };
     *
     * _.pickBy(object, _.isNumber);
     * // => { 'a': 1, 'c': 3 }
     */
    function pickBy(object, predicate) {
      if (object == null) {
        return {};
      }
      var props = arrayMap(getAllKeysIn(object), function(prop) {
        return [prop];
      });
      predicate = getIteratee(predicate);
      return basePickBy(object, props, function(value, path) {
        return predicate(value, path[0]);
      });
    }

    /**
     * This method is like `_.get` except that if the resolved value is a
     * function it's invoked with the `this` binding of its parent object and
     * its result is returned.
     *
     * @static
     * @since 0.1.0
     * @memberOf _
     * @category Object
     * @param {Object} object The object to query.
     * @param {Array|string} path The path of the property to resolve.
     * @param {*} [defaultValue] The value returned for `undefined` resolved values.
     * @returns {*} Returns the resolved value.
     * @example
     *
     * var object = { 'a': [{ 'b': { 'c1': 3, 'c2': _.constant(4) } }] };
     *
     * _.result(object, 'a[0].b.c1');
     * // => 3
     *
     * _.result(object, 'a[0].b.c2');
     * // => 4
     *
     * _.result(object, 'a[0].b.c3', 'default');
     * // => 'default'
     *
     * _.result(object, 'a[0].b.c3', _.constant('default'));
     * // => 'default'
     */
    function result(object, path, defaultValue) {
      path = castPath(path, object);

      var index = -1,
          length = path.length;

      // Ensure the loop is entered when path is empty.
      if (!length) {
        length = 1;
        object = undefined;
      }
      while (++index < length) {
        var value = object == null ? undefined : object[toKey(path[index])];
        if (value === undefined) {
          index = length;
          value = defaultValue;
        }
        object = isFunction(value) ? value.call(object) : value;
      }
      return object;
    }

    /**
     * Sets the value at `path` of `object`. If a portion of `path` doesn't exist,
     * it's created. Arrays are created for missing index properties while objects
     * are created for all other missing properties. Use `_.setWith` to customize
     * `path` creation.
     *
     * **Note:** This method mutates `object`.
     *
     * @static
     * @memberOf _
     * @since 3.7.0
     * @category Object
     * @param {Object} object The object to modify.
     * @param {Array|string} path The path of the property to set.
     * @param {*} value The value to set.
     * @returns {Object} Returns `object`.
     * @example
     *
     * var object = { 'a': [{ 'b': { 'c': 3 } }] };
     *
     * _.set(object, 'a[0].b.c', 4);
     * console.log(object.a[0].b.c);
     * // => 4
     *
     * _.set(object, ['x', '0', 'y', 'z'], 5);
     * console.log(object.x[0].y.z);
     * // => 5
     */
    function set(object, path, value) {
      return object == null ? object : baseSet(object, path, value);
    }

    /**
     * This method is like `_.set` except that it accepts `customizer` which is
     * invoked to produce the objects of `path`.  If `customizer` returns `undefined`
     * path creation is handled by the method instead. The `customizer` is invoked
     * with three arguments: (nsValue, key, nsObject).
     *
     * **Note:** This method mutates `object`.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Object
     * @param {Object} object The object to modify.
     * @param {Array|string} path The path of the property to set.
     * @param {*} value The value to set.
     * @param {Function} [customizer] The function to customize assigned values.
     * @returns {Object} Returns `object`.
     * @example
     *
     * var object = {};
     *
     * _.setWith(object, '[0][1]', 'a', Object);
     * // => { '0': { '1': 'a' } }
     */
    function setWith(object, path, value, customizer) {
      customizer = typeof customizer == 'function' ? customizer : undefined;
      return object == null ? object : baseSet(object, path, value, customizer);
    }

    /**
     * Creates an array of own enumerable string keyed-value pairs for `object`
     * which can be consumed by `_.fromPairs`. If `object` is a map or set, its
     * entries are returned.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @alias entries
     * @category Object
     * @param {Object} object The object to query.
     * @returns {Array} Returns the key-value pairs.
     * @example
     *
     * function Foo() {
     *   this.a = 1;
     *   this.b = 2;
     * }
     *
     * Foo.prototype.c = 3;
     *
     * _.toPairs(new Foo);
     * // => [['a', 1], ['b', 2]] (iteration order is not guaranteed)
     */
    var toPairs = createToPairs(keys);

    /**
     * Creates an array of own and inherited enumerable string keyed-value pairs
     * for `object` which can be consumed by `_.fromPairs`. If `object` is a map
     * or set, its entries are returned.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @alias entriesIn
     * @category Object
     * @param {Object} object The object to query.
     * @returns {Array} Returns the key-value pairs.
     * @example
     *
     * function Foo() {
     *   this.a = 1;
     *   this.b = 2;
     * }
     *
     * Foo.prototype.c = 3;
     *
     * _.toPairsIn(new Foo);
     * // => [['a', 1], ['b', 2], ['c', 3]] (iteration order is not guaranteed)
     */
    var toPairsIn = createToPairs(keysIn);

    /**
     * An alternative to `_.reduce`; this method transforms `object` to a new
     * `accumulator` object which is the result of running each of its own
     * enumerable string keyed properties thru `iteratee`, with each invocation
     * potentially mutating the `accumulator` object. If `accumulator` is not
     * provided, a new object with the same `[[Prototype]]` will be used. The
     * iteratee is invoked with four arguments: (accumulator, value, key, object).
     * Iteratee functions may exit iteration early by explicitly returning `false`.
     *
     * @static
     * @memberOf _
     * @since 1.3.0
     * @category Object
     * @param {Object} object The object to iterate over.
     * @param {Function} [iteratee=_.identity] The function invoked per iteration.
     * @param {*} [accumulator] The custom accumulator value.
     * @returns {*} Returns the accumulated value.
     * @example
     *
     * _.transform([2, 3, 4], function(result, n) {
     *   result.push(n *= n);
     *   return n % 2 == 0;
     * }, []);
     * // => [4, 9]
     *
     * _.transform({ 'a': 1, 'b': 2, 'c': 1 }, function(result, value, key) {
     *   (result[value] || (result[value] = [])).push(key);
     * }, {});
     * // => { '1': ['a', 'c'], '2': ['b'] }
     */
    function transform(object, iteratee, accumulator) {
      var isArr = isArray(object),
          isArrLike = isArr || isBuffer(object) || isTypedArray(object);

      iteratee = getIteratee(iteratee, 4);
      if (accumulator == null) {
        var Ctor = object && object.constructor;
        if (isArrLike) {
          accumulator = isArr ? new Ctor : [];
        }
        else if (isObject(object)) {
          accumulator = isFunction(Ctor) ? baseCreate(getPrototype(object)) : {};
        }
        else {
          accumulator = {};
        }
      }
      (isArrLike ? arrayEach : baseForOwn)(object, function(value, index, object) {
        return iteratee(accumulator, value, index, object);
      });
      return accumulator;
    }

    /**
     * Removes the property at `path` of `object`.
     *
     * **Note:** This method mutates `object`.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Object
     * @param {Object} object The object to modify.
     * @param {Array|string} path The path of the property to unset.
     * @returns {boolean} Returns `true` if the property is deleted, else `false`.
     * @example
     *
     * var object = { 'a': [{ 'b': { 'c': 7 } }] };
     * _.unset(object, 'a[0].b.c');
     * // => true
     *
     * console.log(object);
     * // => { 'a': [{ 'b': {} }] };
     *
     * _.unset(object, ['a', '0', 'b', 'c']);
     * // => true
     *
     * console.log(object);
     * // => { 'a': [{ 'b': {} }] };
     */
    function unset(object, path) {
      return object == null ? true : baseUnset(object, path);
    }

    /**
     * This method is like `_.set` except that accepts `updater` to produce the
     * value to set. Use `_.updateWith` to customize `path` creation. The `updater`
     * is invoked with one argument: (value).
     *
     * **Note:** This method mutates `object`.
     *
     * @static
     * @memberOf _
     * @since 4.6.0
     * @category Object
     * @param {Object} object The object to modify.
     * @param {Array|string} path The path of the property to set.
     * @param {Function} updater The function to produce the updated value.
     * @returns {Object} Returns `object`.
     * @example
     *
     * var object = { 'a': [{ 'b': { 'c': 3 } }] };
     *
     * _.update(object, 'a[0].b.c', function(n) { return n * n; });
     * console.log(object.a[0].b.c);
     * // => 9
     *
     * _.update(object, 'x[0].y.z', function(n) { return n ? n + 1 : 0; });
     * console.log(object.x[0].y.z);
     * // => 0
     */
    function update(object, path, updater) {
      return object == null ? object : baseUpdate(object, path, castFunction(updater));
    }

    /**
     * This method is like `_.update` except that it accepts `customizer` which is
     * invoked to produce the objects of `path`.  If `customizer` returns `undefined`
     * path creation is handled by the method instead. The `customizer` is invoked
     * with three arguments: (nsValue, key, nsObject).
     *
     * **Note:** This method mutates `object`.
     *
     * @static
     * @memberOf _
     * @since 4.6.0
     * @category Object
     * @param {Object} object The object to modify.
     * @param {Array|string} path The path of the property to set.
     * @param {Function} updater The function to produce the updated value.
     * @param {Function} [customizer] The function to customize assigned values.
     * @returns {Object} Returns `object`.
     * @example
     *
     * var object = {};
     *
     * _.updateWith(object, '[0][1]', _.constant('a'), Object);
     * // => { '0': { '1': 'a' } }
     */
    function updateWith(object, path, updater, customizer) {
      customizer = typeof customizer == 'function' ? customizer : undefined;
      return object == null ? object : baseUpdate(object, path, castFunction(updater), customizer);
    }

    /**
     * Creates an array of the own enumerable string keyed property values of `object`.
     *
     * **Note:** Non-object values are coerced to objects.
     *
     * @static
     * @since 0.1.0
     * @memberOf _
     * @category Object
     * @param {Object} object The object to query.
     * @returns {Array} Returns the array of property values.
     * @example
     *
     * function Foo() {
     *   this.a = 1;
     *   this.b = 2;
     * }
     *
     * Foo.prototype.c = 3;
     *
     * _.values(new Foo);
     * // => [1, 2] (iteration order is not guaranteed)
     *
     * _.values('hi');
     * // => ['h', 'i']
     */
    function values(object) {
      return object == null ? [] : baseValues(object, keys(object));
    }

    /**
     * Creates an array of the own and inherited enumerable string keyed property
     * values of `object`.
     *
     * **Note:** Non-object values are coerced to objects.
     *
     * @static
     * @memberOf _
     * @since 3.0.0
     * @category Object
     * @param {Object} object The object to query.
     * @returns {Array} Returns the array of property values.
     * @example
     *
     * function Foo() {
     *   this.a = 1;
     *   this.b = 2;
     * }
     *
     * Foo.prototype.c = 3;
     *
     * _.valuesIn(new Foo);
     * // => [1, 2, 3] (iteration order is not guaranteed)
     */
    function valuesIn(object) {
      return object == null ? [] : baseValues(object, keysIn(object));
    }

    /*------------------------------------------------------------------------*/

    /**
     * Clamps `number` within the inclusive `lower` and `upper` bounds.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Number
     * @param {number} number The number to clamp.
     * @param {number} [lower] The lower bound.
     * @param {number} upper The upper bound.
     * @returns {number} Returns the clamped number.
     * @example
     *
     * _.clamp(-10, -5, 5);
     * // => -5
     *
     * _.clamp(10, -5, 5);
     * // => 5
     */
    function clamp(number, lower, upper) {
      if (upper === undefined) {
        upper = lower;
        lower = undefined;
      }
      if (upper !== undefined) {
        upper = toNumber(upper);
        upper = upper === upper ? upper : 0;
      }
      if (lower !== undefined) {
        lower = toNumber(lower);
        lower = lower === lower ? lower : 0;
      }
      return baseClamp(toNumber(number), lower, upper);
    }

    /**
     * Checks if `n` is between `start` and up to, but not including, `end`. If
     * `end` is not specified, it's set to `start` with `start` then set to `0`.
     * If `start` is greater than `end` the params are swapped to support
     * negative ranges.
     *
     * @static
     * @memberOf _
     * @since 3.3.0
     * @category Number
     * @param {number} number The number to check.
     * @param {number} [start=0] The start of the range.
     * @param {number} end The end of the range.
     * @returns {boolean} Returns `true` if `number` is in the range, else `false`.
     * @see _.range, _.rangeRight
     * @example
     *
     * _.inRange(3, 2, 4);
     * // => true
     *
     * _.inRange(4, 8);
     * // => true
     *
     * _.inRange(4, 2);
     * // => false
     *
     * _.inRange(2, 2);
     * // => false
     *
     * _.inRange(1.2, 2);
     * // => true
     *
     * _.inRange(5.2, 4);
     * // => false
     *
     * _.inRange(-3, -2, -6);
     * // => true
     */
    function inRange(number, start, end) {
      start = toFinite(start);
      if (end === undefined) {
        end = start;
        start = 0;
      } else {
        end = toFinite(end);
      }
      number = toNumber(number);
      return baseInRange(number, start, end);
    }

    /**
     * Produces a random number between the inclusive `lower` and `upper` bounds.
     * If only one argument is provided a number between `0` and the given number
     * is returned. If `floating` is `true`, or either `lower` or `upper` are
     * floats, a floating-point number is returned instead of an integer.
     *
     * **Note:** JavaScript follows the IEEE-754 standard for resolving
     * floating-point values which can produce unexpected results.
     *
     * @static
     * @memberOf _
     * @since 0.7.0
     * @category Number
     * @param {number} [lower=0] The lower bound.
     * @param {number} [upper=1] The upper bound.
     * @param {boolean} [floating] Specify returning a floating-point number.
     * @returns {number} Returns the random number.
     * @example
     *
     * _.random(0, 5);
     * // => an integer between 0 and 5
     *
     * _.random(5);
     * // => also an integer between 0 and 5
     *
     * _.random(5, true);
     * // => a floating-point number between 0 and 5
     *
     * _.random(1.2, 5.2);
     * // => a floating-point number between 1.2 and 5.2
     */
    function random(lower, upper, floating) {
      if (floating && typeof floating != 'boolean' && isIterateeCall(lower, upper, floating)) {
        upper = floating = undefined;
      }
      if (floating === undefined) {
        if (typeof upper == 'boolean') {
          floating = upper;
          upper = undefined;
        }
        else if (typeof lower == 'boolean') {
          floating = lower;
          lower = undefined;
        }
      }
      if (lower === undefined && upper === undefined) {
        lower = 0;
        upper = 1;
      }
      else {
        lower = toFinite(lower);
        if (upper === undefined) {
          upper = lower;
          lower = 0;
        } else {
          upper = toFinite(upper);
        }
      }
      if (lower > upper) {
        var temp = lower;
        lower = upper;
        upper = temp;
      }
      if (floating || lower % 1 || upper % 1) {
        var rand = nativeRandom();
        return nativeMin(lower + (rand * (upper - lower + freeParseFloat('1e-' + ((rand + '').length - 1)))), upper);
      }
      return baseRandom(lower, upper);
    }

    /*------------------------------------------------------------------------*/

    /**
     * Converts `string` to [camel case](https://en.wikipedia.org/wiki/CamelCase).
     *
     * @static
     * @memberOf _
     * @since 3.0.0
     * @category String
     * @param {string} [string=''] The string to convert.
     * @returns {string} Returns the camel cased string.
     * @example
     *
     * _.camelCase('Foo Bar');
     * // => 'fooBar'
     *
     * _.camelCase('--foo-bar--');
     * // => 'fooBar'
     *
     * _.camelCase('__FOO_BAR__');
     * // => 'fooBar'
     */
    var camelCase = createCompounder(function(result, word, index) {
      word = word.toLowerCase();
      return result + (index ? capitalize(word) : word);
    });

    /**
     * Converts the first character of `string` to upper case and the remaining
     * to lower case.
     *
     * @static
     * @memberOf _
     * @since 3.0.0
     * @category String
     * @param {string} [string=''] The string to capitalize.
     * @returns {string} Returns the capitalized string.
     * @example
     *
     * _.capitalize('FRED');
     * // => 'Fred'
     */
    function capitalize(string) {
      return upperFirst(toString(string).toLowerCase());
    }

    /**
     * Deburrs `string` by converting
     * [Latin-1 Supplement](https://en.wikipedia.org/wiki/Latin-1_Supplement_(Unicode_block)#Character_table)
     * and [Latin Extended-A](https://en.wikipedia.org/wiki/Latin_Extended-A)
     * letters to basic Latin letters and removing
     * [combining diacritical marks](https://en.wikipedia.org/wiki/Combining_Diacritical_Marks).
     *
     * @static
     * @memberOf _
     * @since 3.0.0
     * @category String
     * @param {string} [string=''] The string to deburr.
     * @returns {string} Returns the deburred string.
     * @example
     *
     * _.deburr('déjà vu');
     * // => 'deja vu'
     */
    function deburr(string) {
      string = toString(string);
      return string && string.replace(reLatin, deburrLetter).replace(reComboMark, '');
    }

    /**
     * Checks if `string` ends with the given target string.
     *
     * @static
     * @memberOf _
     * @since 3.0.0
     * @category String
     * @param {string} [string=''] The string to inspect.
     * @param {string} [target] The string to search for.
     * @param {number} [position=string.length] The position to search up to.
     * @returns {boolean} Returns `true` if `string` ends with `target`,
     *  else `false`.
     * @example
     *
     * _.endsWith('abc', 'c');
     * // => true
     *
     * _.endsWith('abc', 'b');
     * // => false
     *
     * _.endsWith('abc', 'b', 2);
     * // => true
     */
    function endsWith(string, target, position) {
      string = toString(string);
      target = baseToString(target);

      var length = string.length;
      position = position === undefined
        ? length
        : baseClamp(toInteger(position), 0, length);

      var end = position;
      position -= target.length;
      return position >= 0 && string.slice(position, end) == target;
    }

    /**
     * Converts the characters "&", "<", ">", '"', and "'" in `string` to their
     * corresponding HTML entities.
     *
     * **Note:** No other characters are escaped. To escape additional
     * characters use a third-party library like [_he_](https://mths.be/he).
     *
     * Though the ">" character is escaped for symmetry, characters like
     * ">" and "/" don't need escaping in HTML and have no special meaning
     * unless they're part of a tag or unquoted attribute value. See
     * [Mathias Bynens's article](https://mathiasbynens.be/notes/ambiguous-ampersands)
     * (under "semi-related fun fact") for more details.
     *
     * When working with HTML you should always
     * [quote attribute values](http://wonko.com/post/html-escaping) to reduce
     * XSS vectors.
     *
     * @static
     * @since 0.1.0
     * @memberOf _
     * @category String
     * @param {string} [string=''] The string to escape.
     * @returns {string} Returns the escaped string.
     * @example
     *
     * _.escape('fred, barney, & pebbles');
     * // => 'fred, barney, &amp; pebbles'
     */
    function escape(string) {
      string = toString(string);
      return (string && reHasUnescapedHtml.test(string))
        ? string.replace(reUnescapedHtml, escapeHtmlChar)
        : string;
    }

    /**
     * Escapes the `RegExp` special characters "^", "$", "\", ".", "*", "+",
     * "?", "(", ")", "[", "]", "{", "}", and "|" in `string`.
     *
     * @static
     * @memberOf _
     * @since 3.0.0
     * @category String
     * @param {string} [string=''] The string to escape.
     * @returns {string} Returns the escaped string.
     * @example
     *
     * _.escapeRegExp('[lodash](https://lodash.com/)');
     * // => '\[lodash\]\(https://lodash\.com/\)'
     */
    function escapeRegExp(string) {
      string = toString(string);
      return (string && reHasRegExpChar.test(string))
        ? string.replace(reRegExpChar, '\\$&')
        : string;
    }

    /**
     * Converts `string` to
     * [kebab case](https://en.wikipedia.org/wiki/Letter_case#Special_case_styles).
     *
     * @static
     * @memberOf _
     * @since 3.0.0
     * @category String
     * @param {string} [string=''] The string to convert.
     * @returns {string} Returns the kebab cased string.
     * @example
     *
     * _.kebabCase('Foo Bar');
     * // => 'foo-bar'
     *
     * _.kebabCase('fooBar');
     * // => 'foo-bar'
     *
     * _.kebabCase('__FOO_BAR__');
     * // => 'foo-bar'
     */
    var kebabCase = createCompounder(function(result, word, index) {
      return result + (index ? '-' : '') + word.toLowerCase();
    });

    /**
     * Converts `string`, as space separated words, to lower case.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category String
     * @param {string} [string=''] The string to convert.
     * @returns {string} Returns the lower cased string.
     * @example
     *
     * _.lowerCase('--Foo-Bar--');
     * // => 'foo bar'
     *
     * _.lowerCase('fooBar');
     * // => 'foo bar'
     *
     * _.lowerCase('__FOO_BAR__');
     * // => 'foo bar'
     */
    var lowerCase = createCompounder(function(result, word, index) {
      return result + (index ? ' ' : '') + word.toLowerCase();
    });

    /**
     * Converts the first character of `string` to lower case.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category String
     * @param {string} [string=''] The string to convert.
     * @returns {string} Returns the converted string.
     * @example
     *
     * _.lowerFirst('Fred');
     * // => 'fred'
     *
     * _.lowerFirst('FRED');
     * // => 'fRED'
     */
    var lowerFirst = createCaseFirst('toLowerCase');

    /**
     * Pads `string` on the left and right sides if it's shorter than `length`.
     * Padding characters are truncated if they can't be evenly divided by `length`.
     *
     * @static
     * @memberOf _
     * @since 3.0.0
     * @category String
     * @param {string} [string=''] The string to pad.
     * @param {number} [length=0] The padding length.
     * @param {string} [chars=' '] The string used as padding.
     * @returns {string} Returns the padded string.
     * @example
     *
     * _.pad('abc', 8);
     * // => '  abc   '
     *
     * _.pad('abc', 8, '_-');
     * // => '_-abc_-_'
     *
     * _.pad('abc', 3);
     * // => 'abc'
     */
    function pad(string, length, chars) {
      string = toString(string);
      length = toInteger(length);

      var strLength = length ? stringSize(string) : 0;
      if (!length || strLength >= length) {
        return string;
      }
      var mid = (length - strLength) / 2;
      return (
        createPadding(nativeFloor(mid), chars) +
        string +
        createPadding(nativeCeil(mid), chars)
      );
    }

    /**
     * Pads `string` on the right side if it's shorter than `length`. Padding
     * characters are truncated if they exceed `length`.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category String
     * @param {string} [string=''] The string to pad.
     * @param {number} [length=0] The padding length.
     * @param {string} [chars=' '] The string used as padding.
     * @returns {string} Returns the padded string.
     * @example
     *
     * _.padEnd('abc', 6);
     * // => 'abc   '
     *
     * _.padEnd('abc', 6, '_-');
     * // => 'abc_-_'
     *
     * _.padEnd('abc', 3);
     * // => 'abc'
     */
    function padEnd(string, length, chars) {
      string = toString(string);
      length = toInteger(length);

      var strLength = length ? stringSize(string) : 0;
      return (length && strLength < length)
        ? (string + createPadding(length - strLength, chars))
        : string;
    }

    /**
     * Pads `string` on the left side if it's shorter than `length`. Padding
     * characters are truncated if they exceed `length`.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category String
     * @param {string} [string=''] The string to pad.
     * @param {number} [length=0] The padding length.
     * @param {string} [chars=' '] The string used as padding.
     * @returns {string} Returns the padded string.
     * @example
     *
     * _.padStart('abc', 6);
     * // => '   abc'
     *
     * _.padStart('abc', 6, '_-');
     * // => '_-_abc'
     *
     * _.padStart('abc', 3);
     * // => 'abc'
     */
    function padStart(string, length, chars) {
      string = toString(string);
      length = toInteger(length);

      var strLength = length ? stringSize(string) : 0;
      return (length && strLength < length)
        ? (createPadding(length - strLength, chars) + string)
        : string;
    }

    /**
     * Converts `string` to an integer of the specified radix. If `radix` is
     * `undefined` or `0`, a `radix` of `10` is used unless `value` is a
     * hexadecimal, in which case a `radix` of `16` is used.
     *
     * **Note:** This method aligns with the
     * [ES5 implementation](https://es5.github.io/#x15.1.2.2) of `parseInt`.
     *
     * @static
     * @memberOf _
     * @since 1.1.0
     * @category String
     * @param {string} string The string to convert.
     * @param {number} [radix=10] The radix to interpret `value` by.
     * @param- {Object} [guard] Enables use as an iteratee for methods like `_.map`.
     * @returns {number} Returns the converted integer.
     * @example
     *
     * _.parseInt('08');
     * // => 8
     *
     * _.map(['6', '08', '10'], _.parseInt);
     * // => [6, 8, 10]
     */
    function parseInt(string, radix, guard) {
      if (guard || radix == null) {
        radix = 0;
      } else if (radix) {
        radix = +radix;
      }
      return nativeParseInt(toString(string).replace(reTrimStart, ''), radix || 0);
    }

    /**
     * Repeats the given string `n` times.
     *
     * @static
     * @memberOf _
     * @since 3.0.0
     * @category String
     * @param {string} [string=''] The string to repeat.
     * @param {number} [n=1] The number of times to repeat the string.
     * @param- {Object} [guard] Enables use as an iteratee for methods like `_.map`.
     * @returns {string} Returns the repeated string.
     * @example
     *
     * _.repeat('*', 3);
     * // => '***'
     *
     * _.repeat('abc', 2);
     * // => 'abcabc'
     *
     * _.repeat('abc', 0);
     * // => ''
     */
    function repeat(string, n, guard) {
      if ((guard ? isIterateeCall(string, n, guard) : n === undefined)) {
        n = 1;
      } else {
        n = toInteger(n);
      }
      return baseRepeat(toString(string), n);
    }

    /**
     * Replaces matches for `pattern` in `string` with `replacement`.
     *
     * **Note:** This method is based on
     * [`String#replace`](https://mdn.io/String/replace).
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category String
     * @param {string} [string=''] The string to modify.
     * @param {RegExp|string} pattern The pattern to replace.
     * @param {Function|string} replacement The match replacement.
     * @returns {string} Returns the modified string.
     * @example
     *
     * _.replace('Hi Fred', 'Fred', 'Barney');
     * // => 'Hi Barney'
     */
    function replace() {
      var args = arguments,
          string = toString(args[0]);

      return args.length < 3 ? string : string.replace(args[1], args[2]);
    }

    /**
     * Converts `string` to
     * [snake case](https://en.wikipedia.org/wiki/Snake_case).
     *
     * @static
     * @memberOf _
     * @since 3.0.0
     * @category String
     * @param {string} [string=''] The string to convert.
     * @returns {string} Returns the snake cased string.
     * @example
     *
     * _.snakeCase('Foo Bar');
     * // => 'foo_bar'
     *
     * _.snakeCase('fooBar');
     * // => 'foo_bar'
     *
     * _.snakeCase('--FOO-BAR--');
     * // => 'foo_bar'
     */
    var snakeCase = createCompounder(function(result, word, index) {
      return result + (index ? '_' : '') + word.toLowerCase();
    });

    /**
     * Splits `string` by `separator`.
     *
     * **Note:** This method is based on
     * [`String#split`](https://mdn.io/String/split).
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category String
     * @param {string} [string=''] The string to split.
     * @param {RegExp|string} separator The separator pattern to split by.
     * @param {number} [limit] The length to truncate results to.
     * @returns {Array} Returns the string segments.
     * @example
     *
     * _.split('a-b-c', '-', 2);
     * // => ['a', 'b']
     */
    function split(string, separator, limit) {
      if (limit && typeof limit != 'number' && isIterateeCall(string, separator, limit)) {
        separator = limit = undefined;
      }
      limit = limit === undefined ? MAX_ARRAY_LENGTH : limit >>> 0;
      if (!limit) {
        return [];
      }
      string = toString(string);
      if (string && (
            typeof separator == 'string' ||
            (separator != null && !isRegExp(separator))
          )) {
        separator = baseToString(separator);
        if (!separator && hasUnicode(string)) {
          return castSlice(stringToArray(string), 0, limit);
        }
      }
      return string.split(separator, limit);
    }

    /**
     * Converts `string` to
     * [start case](https://en.wikipedia.org/wiki/Letter_case#Stylistic_or_specialised_usage).
     *
     * @static
     * @memberOf _
     * @since 3.1.0
     * @category String
     * @param {string} [string=''] The string to convert.
     * @returns {string} Returns the start cased string.
     * @example
     *
     * _.startCase('--foo-bar--');
     * // => 'Foo Bar'
     *
     * _.startCase('fooBar');
     * // => 'Foo Bar'
     *
     * _.startCase('__FOO_BAR__');
     * // => 'FOO BAR'
     */
    var startCase = createCompounder(function(result, word, index) {
      return result + (index ? ' ' : '') + upperFirst(word);
    });

    /**
     * Checks if `string` starts with the given target string.
     *
     * @static
     * @memberOf _
     * @since 3.0.0
     * @category String
     * @param {string} [string=''] The string to inspect.
     * @param {string} [target] The string to search for.
     * @param {number} [position=0] The position to search from.
     * @returns {boolean} Returns `true` if `string` starts with `target`,
     *  else `false`.
     * @example
     *
     * _.startsWith('abc', 'a');
     * // => true
     *
     * _.startsWith('abc', 'b');
     * // => false
     *
     * _.startsWith('abc', 'b', 1);
     * // => true
     */
    function startsWith(string, target, position) {
      string = toString(string);
      position = position == null
        ? 0
        : baseClamp(toInteger(position), 0, string.length);

      target = baseToString(target);
      return string.slice(position, position + target.length) == target;
    }

    /**
     * Creates a compiled template function that can interpolate data properties
     * in "interpolate" delimiters, HTML-escape interpolated data properties in
     * "escape" delimiters, and execute JavaScript in "evaluate" delimiters. Data
     * properties may be accessed as free variables in the template. If a setting
     * object is given, it takes precedence over `_.templateSettings` values.
     *
     * **Note:** In the development build `_.template` utilizes
     * [sourceURLs](http://www.html5rocks.com/en/tutorials/developertools/sourcemaps/#toc-sourceurl)
     * for easier debugging.
     *
     * For more information on precompiling templates see
     * [lodash's custom builds documentation](https://lodash.com/custom-builds).
     *
     * For more information on Chrome extension sandboxes see
     * [Chrome's extensions documentation](https://developer.chrome.com/extensions/sandboxingEval).
     *
     * @static
     * @since 0.1.0
     * @memberOf _
     * @category String
     * @param {string} [string=''] The template string.
     * @param {Object} [options={}] The options object.
     * @param {RegExp} [options.escape=_.templateSettings.escape]
     *  The HTML "escape" delimiter.
     * @param {RegExp} [options.evaluate=_.templateSettings.evaluate]
     *  The "evaluate" delimiter.
     * @param {Object} [options.imports=_.templateSettings.imports]
     *  An object to import into the template as free variables.
     * @param {RegExp} [options.interpolate=_.templateSettings.interpolate]
     *  The "interpolate" delimiter.
     * @param {string} [options.sourceURL='lodash.templateSources[n]']
     *  The sourceURL of the compiled template.
     * @param {string} [options.variable='obj']
     *  The data object variable name.
     * @param- {Object} [guard] Enables use as an iteratee for methods like `_.map`.
     * @returns {Function} Returns the compiled template function.
     * @example
     *
     * // Use the "interpolate" delimiter to create a compiled template.
     * var compiled = _.template('hello <%= user %>!');
     * compiled({ 'user': 'fred' });
     * // => 'hello fred!'
     *
     * // Use the HTML "escape" delimiter to escape data property values.
     * var compiled = _.template('<b><%- value %></b>');
     * compiled({ 'value': '<script>' });
     * // => '<b>&lt;script&gt;</b>'
     *
     * // Use the "evaluate" delimiter to execute JavaScript and generate HTML.
     * var compiled = _.template('<% _.forEach(users, function(user) { %><li><%- user %></li><% }); %>');
     * compiled({ 'users': ['fred', 'barney'] });
     * // => '<li>fred</li><li>barney</li>'
     *
     * // Use the internal `print` function in "evaluate" delimiters.
     * var compiled = _.template('<% print("hello " + user); %>!');
     * compiled({ 'user': 'barney' });
     * // => 'hello barney!'
     *
     * // Use the ES template literal delimiter as an "interpolate" delimiter.
     * // Disable support by replacing the "interpolate" delimiter.
     * var compiled = _.template('hello ${ user }!');
     * compiled({ 'user': 'pebbles' });
     * // => 'hello pebbles!'
     *
     * // Use backslashes to treat delimiters as plain text.
     * var compiled = _.template('<%= "\\<%- value %\\>" %>');
     * compiled({ 'value': 'ignored' });
     * // => '<%- value %>'
     *
     * // Use the `imports` option to import `jQuery` as `jq`.
     * var text = '<% jq.each(users, function(user) { %><li><%- user %></li><% }); %>';
     * var compiled = _.template(text, { 'imports': { 'jq': jQuery } });
     * compiled({ 'users': ['fred', 'barney'] });
     * // => '<li>fred</li><li>barney</li>'
     *
     * // Use the `sourceURL` option to specify a custom sourceURL for the template.
     * var compiled = _.template('hello <%= user %>!', { 'sourceURL': '/basic/greeting.jst' });
     * compiled(data);
     * // => Find the source of "greeting.jst" under the Sources tab or Resources panel of the web inspector.
     *
     * // Use the `variable` option to ensure a with-statement isn't used in the compiled template.
     * var compiled = _.template('hi <%= data.user %>!', { 'variable': 'data' });
     * compiled.source;
     * // => function(data) {
     * //   var __t, __p = '';
     * //   __p += 'hi ' + ((__t = ( data.user )) == null ? '' : __t) + '!';
     * //   return __p;
     * // }
     *
     * // Use custom template delimiters.
     * _.templateSettings.interpolate = /{{([\s\S]+?)}}/g;
     * var compiled = _.template('hello {{ user }}!');
     * compiled({ 'user': 'mustache' });
     * // => 'hello mustache!'
     *
     * // Use the `source` property to inline compiled templates for meaningful
     * // line numbers in error messages and stack traces.
     * fs.writeFileSync(path.join(process.cwd(), 'jst.js'), '\
     *   var JST = {\
     *     "main": ' + _.template(mainText).source + '\
     *   };\
     * ');
     */
    function template(string, options, guard) {
      // Based on John Resig's `tmpl` implementation
      // (http://ejohn.org/blog/javascript-micro-templating/)
      // and Laura Doktorova's doT.js (https://github.com/olado/doT).
      var settings = lodash.templateSettings;

      if (guard && isIterateeCall(string, options, guard)) {
        options = undefined;
      }
      string = toString(string);
      options = assignInWith({}, options, settings, customDefaultsAssignIn);

      var imports = assignInWith({}, options.imports, settings.imports, customDefaultsAssignIn),
          importsKeys = keys(imports),
          importsValues = baseValues(imports, importsKeys);

      var isEscaping,
          isEvaluating,
          index = 0,
          interpolate = options.interpolate || reNoMatch,
          source = "__p += '";

      // Compile the regexp to match each delimiter.
      var reDelimiters = RegExp(
        (options.escape || reNoMatch).source + '|' +
        interpolate.source + '|' +
        (interpolate === reInterpolate ? reEsTemplate : reNoMatch).source + '|' +
        (options.evaluate || reNoMatch).source + '|$'
      , 'g');

      // Use a sourceURL for easier debugging.
      // The sourceURL gets injected into the source that's eval-ed, so be careful
      // to normalize all kinds of whitespace, so e.g. newlines (and unicode versions of it) can't sneak in
      // and escape the comment, thus injecting code that gets evaled.
      var sourceURL = '//# sourceURL=' +
        (hasOwnProperty.call(options, 'sourceURL')
          ? (options.sourceURL + '').replace(/\s/g, ' ')
          : ('lodash.templateSources[' + (++templateCounter) + ']')
        ) + '\n';

      string.replace(reDelimiters, function(match, escapeValue, interpolateValue, esTemplateValue, evaluateValue, offset) {
        interpolateValue || (interpolateValue = esTemplateValue);

        // Escape characters that can't be included in string literals.
        source += string.slice(index, offset).replace(reUnescapedString, escapeStringChar);

        // Replace delimiters with snippets.
        if (escapeValue) {
          isEscaping = true;
          source += "' +\n__e(" + escapeValue + ") +\n'";
        }
        if (evaluateValue) {
          isEvaluating = true;
          source += "';\n" + evaluateValue + ";\n__p += '";
        }
        if (interpolateValue) {
          source += "' +\n((__t = (" + interpolateValue + ")) == null ? '' : __t) +\n'";
        }
        index = offset + match.length;

        // The JS engine embedded in Adobe products needs `match` returned in
        // order to produce the correct `offset` value.
        return match;
      });

      source += "';\n";

      // If `variable` is not specified wrap a with-statement around the generated
      // code to add the data object to the top of the scope chain.
      var variable = hasOwnProperty.call(options, 'variable') && options.variable;
      if (!variable) {
        source = 'with (obj) {\n' + source + '\n}\n';
      }
      // Throw an error if a forbidden character was found in `variable`, to prevent
      // potential command injection attacks.
      else if (reForbiddenIdentifierChars.test(variable)) {
        throw new Error(INVALID_TEMPL_VAR_ERROR_TEXT);
      }

      // Cleanup code by stripping empty strings.
      source = (isEvaluating ? source.replace(reEmptyStringLeading, '') : source)
        .replace(reEmptyStringMiddle, '$1')
        .replace(reEmptyStringTrailing, '$1;');

      // Frame code as the function body.
      source = 'function(' + (variable || 'obj') + ') {\n' +
        (variable
          ? ''
          : 'obj || (obj = {});\n'
        ) +
        "var __t, __p = ''" +
        (isEscaping
           ? ', __e = _.escape'
           : ''
        ) +
        (isEvaluating
          ? ', __j = Array.prototype.join;\n' +
            "function print() { __p += __j.call(arguments, '') }\n"
          : ';\n'
        ) +
        source +
        'return __p\n}';

      var result = attempt(function() {
        return Function(importsKeys, sourceURL + 'return ' + source)
          .apply(undefined, importsValues);
      });

      // Provide the compiled function's source by its `toString` method or
      // the `source` property as a convenience for inlining compiled templates.
      result.source = source;
      if (isError(result)) {
        throw result;
      }
      return result;
    }

    /**
     * Converts `string`, as a whole, to lower case just like
     * [String#toLowerCase](https://mdn.io/toLowerCase).
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category String
     * @param {string} [string=''] The string to convert.
     * @returns {string} Returns the lower cased string.
     * @example
     *
     * _.toLower('--Foo-Bar--');
     * // => '--foo-bar--'
     *
     * _.toLower('fooBar');
     * // => 'foobar'
     *
     * _.toLower('__FOO_BAR__');
     * // => '__foo_bar__'
     */
    function toLower(value) {
      return toString(value).toLowerCase();
    }

    /**
     * Converts `string`, as a whole, to upper case just like
     * [String#toUpperCase](https://mdn.io/toUpperCase).
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category String
     * @param {string} [string=''] The string to convert.
     * @returns {string} Returns the upper cased string.
     * @example
     *
     * _.toUpper('--foo-bar--');
     * // => '--FOO-BAR--'
     *
     * _.toUpper('fooBar');
     * // => 'FOOBAR'
     *
     * _.toUpper('__foo_bar__');
     * // => '__FOO_BAR__'
     */
    function toUpper(value) {
      return toString(value).toUpperCase();
    }

    /**
     * Removes leading and trailing whitespace or specified characters from `string`.
     *
     * @static
     * @memberOf _
     * @since 3.0.0
     * @category String
     * @param {string} [string=''] The string to trim.
     * @param {string} [chars=whitespace] The characters to trim.
     * @param- {Object} [guard] Enables use as an iteratee for methods like `_.map`.
     * @returns {string} Returns the trimmed string.
     * @example
     *
     * _.trim('  abc  ');
     * // => 'abc'
     *
     * _.trim('-_-abc-_-', '_-');
     * // => 'abc'
     *
     * _.map(['  foo  ', '  bar  '], _.trim);
     * // => ['foo', 'bar']
     */
    function trim(string, chars, guard) {
      string = toString(string);
      if (string && (guard || chars === undefined)) {
        return baseTrim(string);
      }
      if (!string || !(chars = baseToString(chars))) {
        return string;
      }
      var strSymbols = stringToArray(string),
          chrSymbols = stringToArray(chars),
          start = charsStartIndex(strSymbols, chrSymbols),
          end = charsEndIndex(strSymbols, chrSymbols) + 1;

      return castSlice(strSymbols, start, end).join('');
    }

    /**
     * Removes trailing whitespace or specified characters from `string`.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category String
     * @param {string} [string=''] The string to trim.
     * @param {string} [chars=whitespace] The characters to trim.
     * @param- {Object} [guard] Enables use as an iteratee for methods like `_.map`.
     * @returns {string} Returns the trimmed string.
     * @example
     *
     * _.trimEnd('  abc  ');
     * // => '  abc'
     *
     * _.trimEnd('-_-abc-_-', '_-');
     * // => '-_-abc'
     */
    function trimEnd(string, chars, guard) {
      string = toString(string);
      if (string && (guard || chars === undefined)) {
        return string.slice(0, trimmedEndIndex(string) + 1);
      }
      if (!string || !(chars = baseToString(chars))) {
        return string;
      }
      var strSymbols = stringToArray(string),
          end = charsEndIndex(strSymbols, stringToArray(chars)) + 1;

      return castSlice(strSymbols, 0, end).join('');
    }

    /**
     * Removes leading whitespace or specified characters from `string`.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category String
     * @param {string} [string=''] The string to trim.
     * @param {string} [chars=whitespace] The characters to trim.
     * @param- {Object} [guard] Enables use as an iteratee for methods like `_.map`.
     * @returns {string} Returns the trimmed string.
     * @example
     *
     * _.trimStart('  abc  ');
     * // => 'abc  '
     *
     * _.trimStart('-_-abc-_-', '_-');
     * // => 'abc-_-'
     */
    function trimStart(string, chars, guard) {
      string = toString(string);
      if (string && (guard || chars === undefined)) {
        return string.replace(reTrimStart, '');
      }
      if (!string || !(chars = baseToString(chars))) {
        return string;
      }
      var strSymbols = stringToArray(string),
          start = charsStartIndex(strSymbols, stringToArray(chars));

      return castSlice(strSymbols, start).join('');
    }

    /**
     * Truncates `string` if it's longer than the given maximum string length.
     * The last characters of the truncated string are replaced with the omission
     * string which defaults to "...".
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category String
     * @param {string} [string=''] The string to truncate.
     * @param {Object} [options={}] The options object.
     * @param {number} [options.length=30] The maximum string length.
     * @param {string} [options.omission='...'] The string to indicate text is omitted.
     * @param {RegExp|string} [options.separator] The separator pattern to truncate to.
     * @returns {string} Returns the truncated string.
     * @example
     *
     * _.truncate('hi-diddly-ho there, neighborino');
     * // => 'hi-diddly-ho there, neighbo...'
     *
     * _.truncate('hi-diddly-ho there, neighborino', {
     *   'length': 24,
     *   'separator': ' '
     * });
     * // => 'hi-diddly-ho there,...'
     *
     * _.truncate('hi-diddly-ho there, neighborino', {
     *   'length': 24,
     *   'separator': /,? +/
     * });
     * // => 'hi-diddly-ho there...'
     *
     * _.truncate('hi-diddly-ho there, neighborino', {
     *   'omission': ' [...]'
     * });
     * // => 'hi-diddly-ho there, neig [...]'
     */
    function truncate(string, options) {
      var length = DEFAULT_TRUNC_LENGTH,
          omission = DEFAULT_TRUNC_OMISSION;

      if (isObject(options)) {
        var separator = 'separator' in options ? options.separator : separator;
        length = 'length' in options ? toInteger(options.length) : length;
        omission = 'omission' in options ? baseToString(options.omission) : omission;
      }
      string = toString(string);

      var strLength = string.length;
      if (hasUnicode(string)) {
        var strSymbols = stringToArray(string);
        strLength = strSymbols.length;
      }
      if (length >= strLength) {
        return string;
      }
      var end = length - stringSize(omission);
      if (end < 1) {
        return omission;
      }
      var result = strSymbols
        ? castSlice(strSymbols, 0, end).join('')
        : string.slice(0, end);

      if (separator === undefined) {
        return result + omission;
      }
      if (strSymbols) {
        end += (result.length - end);
      }
      if (isRegExp(separator)) {
        if (string.slice(end).search(separator)) {
          var match,
              substring = result;

          if (!separator.global) {
            separator = RegExp(separator.source, toString(reFlags.exec(separator)) + 'g');
          }
          separator.lastIndex = 0;
          while ((match = separator.exec(substring))) {
            var newEnd = match.index;
          }
          result = result.slice(0, newEnd === undefined ? end : newEnd);
        }
      } else if (string.indexOf(baseToString(separator), end) != end) {
        var index = result.lastIndexOf(separator);
        if (index > -1) {
          result = result.slice(0, index);
        }
      }
      return result + omission;
    }

    /**
     * The inverse of `_.escape`; this method converts the HTML entities
     * `&amp;`, `&lt;`, `&gt;`, `&quot;`, and `&#39;` in `string` to
     * their corresponding characters.
     *
     * **Note:** No other HTML entities are unescaped. To unescape additional
     * HTML entities use a third-party library like [_he_](https://mths.be/he).
     *
     * @static
     * @memberOf _
     * @since 0.6.0
     * @category String
     * @param {string} [string=''] The string to unescape.
     * @returns {string} Returns the unescaped string.
     * @example
     *
     * _.unescape('fred, barney, &amp; pebbles');
     * // => 'fred, barney, & pebbles'
     */
    function unescape(string) {
      string = toString(string);
      return (string && reHasEscapedHtml.test(string))
        ? string.replace(reEscapedHtml, unescapeHtmlChar)
        : string;
    }

    /**
     * Converts `string`, as space separated words, to upper case.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category String
     * @param {string} [string=''] The string to convert.
     * @returns {string} Returns the upper cased string.
     * @example
     *
     * _.upperCase('--foo-bar');
     * // => 'FOO BAR'
     *
     * _.upperCase('fooBar');
     * // => 'FOO BAR'
     *
     * _.upperCase('__foo_bar__');
     * // => 'FOO BAR'
     */
    var upperCase = createCompounder(function(result, word, index) {
      return result + (index ? ' ' : '') + word.toUpperCase();
    });

    /**
     * Converts the first character of `string` to upper case.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category String
     * @param {string} [string=''] The string to convert.
     * @returns {string} Returns the converted string.
     * @example
     *
     * _.upperFirst('fred');
     * // => 'Fred'
     *
     * _.upperFirst('FRED');
     * // => 'FRED'
     */
    var upperFirst = createCaseFirst('toUpperCase');

    /**
     * Splits `string` into an array of its words.
     *
     * @static
     * @memberOf _
     * @since 3.0.0
     * @category String
     * @param {string} [string=''] The string to inspect.
     * @param {RegExp|string} [pattern] The pattern to match words.
     * @param- {Object} [guard] Enables use as an iteratee for methods like `_.map`.
     * @returns {Array} Returns the words of `string`.
     * @example
     *
     * _.words('fred, barney, & pebbles');
     * // => ['fred', 'barney', 'pebbles']
     *
     * _.words('fred, barney, & pebbles', /[^, ]+/g);
     * // => ['fred', 'barney', '&', 'pebbles']
     */
    function words(string, pattern, guard) {
      string = toString(string);
      pattern = guard ? undefined : pattern;

      if (pattern === undefined) {
        return hasUnicodeWord(string) ? unicodeWords(string) : asciiWords(string);
      }
      return string.match(pattern) || [];
    }

    /*------------------------------------------------------------------------*/

    /**
     * Attempts to invoke `func`, returning either the result or the caught error
     * object. Any additional arguments are provided to `func` when it's invoked.
     *
     * @static
     * @memberOf _
     * @since 3.0.0
     * @category Util
     * @param {Function} func The function to attempt.
     * @param {...*} [args] The arguments to invoke `func` with.
     * @returns {*} Returns the `func` result or error object.
     * @example
     *
     * // Avoid throwing errors for invalid selectors.
     * var elements = _.attempt(function(selector) {
     *   return document.querySelectorAll(selector);
     * }, '>_>');
     *
     * if (_.isError(elements)) {
     *   elements = [];
     * }
     */
    var attempt = baseRest(function(func, args) {
      try {
        return apply(func, undefined, args);
      } catch (e) {
        return isError(e) ? e : new Error(e);
      }
    });

    /**
     * Binds methods of an object to the object itself, overwriting the existing
     * method.
     *
     * **Note:** This method doesn't set the "length" property of bound functions.
     *
     * @static
     * @since 0.1.0
     * @memberOf _
     * @category Util
     * @param {Object} object The object to bind and assign the bound methods to.
     * @param {...(string|string[])} methodNames The object method names to bind.
     * @returns {Object} Returns `object`.
     * @example
     *
     * var view = {
     *   'label': 'docs',
     *   'click': function() {
     *     console.log('clicked ' + this.label);
     *   }
     * };
     *
     * _.bindAll(view, ['click']);
     * jQuery(element).on('click', view.click);
     * // => Logs 'clicked docs' when clicked.
     */
    var bindAll = flatRest(function(object, methodNames) {
      arrayEach(methodNames, function(key) {
        key = toKey(key);
        baseAssignValue(object, key, bind(object[key], object));
      });
      return object;
    });

    /**
     * Creates a function that iterates over `pairs` and invokes the corresponding
     * function of the first predicate to return truthy. The predicate-function
     * pairs are invoked with the `this` binding and arguments of the created
     * function.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Util
     * @param {Array} pairs The predicate-function pairs.
     * @returns {Function} Returns the new composite function.
     * @example
     *
     * var func = _.cond([
     *   [_.matches({ 'a': 1 }),           _.constant('matches A')],
     *   [_.conforms({ 'b': _.isNumber }), _.constant('matches B')],
     *   [_.stubTrue,                      _.constant('no match')]
     * ]);
     *
     * func({ 'a': 1, 'b': 2 });
     * // => 'matches A'
     *
     * func({ 'a': 0, 'b': 1 });
     * // => 'matches B'
     *
     * func({ 'a': '1', 'b': '2' });
     * // => 'no match'
     */
    function cond(pairs) {
      var length = pairs == null ? 0 : pairs.length,
          toIteratee = getIteratee();

      pairs = !length ? [] : arrayMap(pairs, function(pair) {
        if (typeof pair[1] != 'function') {
          throw new TypeError(FUNC_ERROR_TEXT);
        }
        return [toIteratee(pair[0]), pair[1]];
      });

      return baseRest(function(args) {
        var index = -1;
        while (++index < length) {
          var pair = pairs[index];
          if (apply(pair[0], this, args)) {
            return apply(pair[1], this, args);
          }
        }
      });
    }

    /**
     * Creates a function that invokes the predicate properties of `source` with
     * the corresponding property values of a given object, returning `true` if
     * all predicates return truthy, else `false`.
     *
     * **Note:** The created function is equivalent to `_.conformsTo` with
     * `source` partially applied.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Util
     * @param {Object} source The object of property predicates to conform to.
     * @returns {Function} Returns the new spec function.
     * @example
     *
     * var objects = [
     *   { 'a': 2, 'b': 1 },
     *   { 'a': 1, 'b': 2 }
     * ];
     *
     * _.filter(objects, _.conforms({ 'b': function(n) { return n > 1; } }));
     * // => [{ 'a': 1, 'b': 2 }]
     */
    function conforms(source) {
      return baseConforms(baseClone(source, CLONE_DEEP_FLAG));
    }

    /**
     * Creates a function that returns `value`.
     *
     * @static
     * @memberOf _
     * @since 2.4.0
     * @category Util
     * @param {*} value The value to return from the new function.
     * @returns {Function} Returns the new constant function.
     * @example
     *
     * var objects = _.times(2, _.constant({ 'a': 1 }));
     *
     * console.log(objects);
     * // => [{ 'a': 1 }, { 'a': 1 }]
     *
     * console.log(objects[0] === objects[1]);
     * // => true
     */
    function constant(value) {
      return function() {
        return value;
      };
    }

    /**
     * Checks `value` to determine whether a default value should be returned in
     * its place. The `defaultValue` is returned if `value` is `NaN`, `null`,
     * or `undefined`.
     *
     * @static
     * @memberOf _
     * @since 4.14.0
     * @category Util
     * @param {*} value The value to check.
     * @param {*} defaultValue The default value.
     * @returns {*} Returns the resolved value.
     * @example
     *
     * _.defaultTo(1, 10);
     * // => 1
     *
     * _.defaultTo(undefined, 10);
     * // => 10
     */
    function defaultTo(value, defaultValue) {
      return (value == null || value !== value) ? defaultValue : value;
    }

    /**
     * Creates a function that returns the result of invoking the given functions
     * with the `this` binding of the created function, where each successive
     * invocation is supplied the return value of the previous.
     *
     * @static
     * @memberOf _
     * @since 3.0.0
     * @category Util
     * @param {...(Function|Function[])} [funcs] The functions to invoke.
     * @returns {Function} Returns the new composite function.
     * @see _.flowRight
     * @example
     *
     * function square(n) {
     *   return n * n;
     * }
     *
     * var addSquare = _.flow([_.add, square]);
     * addSquare(1, 2);
     * // => 9
     */
    var flow = createFlow();

    /**
     * This method is like `_.flow` except that it creates a function that
     * invokes the given functions from right to left.
     *
     * @static
     * @since 3.0.0
     * @memberOf _
     * @category Util
     * @param {...(Function|Function[])} [funcs] The functions to invoke.
     * @returns {Function} Returns the new composite function.
     * @see _.flow
     * @example
     *
     * function square(n) {
     *   return n * n;
     * }
     *
     * var addSquare = _.flowRight([square, _.add]);
     * addSquare(1, 2);
     * // => 9
     */
    var flowRight = createFlow(true);

    /**
     * This method returns the first argument it receives.
     *
     * @static
     * @since 0.1.0
     * @memberOf _
     * @category Util
     * @param {*} value Any value.
     * @returns {*} Returns `value`.
     * @example
     *
     * var object = { 'a': 1 };
     *
     * console.log(_.identity(object) === object);
     * // => true
     */
    function identity(value) {
      return value;
    }

    /**
     * Creates a function that invokes `func` with the arguments of the created
     * function. If `func` is a property name, the created function returns the
     * property value for a given element. If `func` is an array or object, the
     * created function returns `true` for elements that contain the equivalent
     * source properties, otherwise it returns `false`.
     *
     * @static
     * @since 4.0.0
     * @memberOf _
     * @category Util
     * @param {*} [func=_.identity] The value to convert to a callback.
     * @returns {Function} Returns the callback.
     * @example
     *
     * var users = [
     *   { 'user': 'barney', 'age': 36, 'active': true },
     *   { 'user': 'fred',   'age': 40, 'active': false }
     * ];
     *
     * // The `_.matches` iteratee shorthand.
     * _.filter(users, _.iteratee({ 'user': 'barney', 'active': true }));
     * // => [{ 'user': 'barney', 'age': 36, 'active': true }]
     *
     * // The `_.matchesProperty` iteratee shorthand.
     * _.filter(users, _.iteratee(['user', 'fred']));
     * // => [{ 'user': 'fred', 'age': 40 }]
     *
     * // The `_.property` iteratee shorthand.
     * _.map(users, _.iteratee('user'));
     * // => ['barney', 'fred']
     *
     * // Create custom iteratee shorthands.
     * _.iteratee = _.wrap(_.iteratee, function(iteratee, func) {
     *   return !_.isRegExp(func) ? iteratee(func) : function(string) {
     *     return func.test(string);
     *   };
     * });
     *
     * _.filter(['abc', 'def'], /ef/);
     * // => ['def']
     */
    function iteratee(func) {
      return baseIteratee(typeof func == 'function' ? func : baseClone(func, CLONE_DEEP_FLAG));
    }

    /**
     * Creates a function that performs a partial deep comparison between a given
     * object and `source`, returning `true` if the given object has equivalent
     * property values, else `false`.
     *
     * **Note:** The created function is equivalent to `_.isMatch` with `source`
     * partially applied.
     *
     * Partial comparisons will match empty array and empty object `source`
     * values against any array or object value, respectively. See `_.isEqual`
     * for a list of supported value comparisons.
     *
     * **Note:** Multiple values can be checked by combining several matchers
     * using `_.overSome`
     *
     * @static
     * @memberOf _
     * @since 3.0.0
     * @category Util
     * @param {Object} source The object of property values to match.
     * @returns {Function} Returns the new spec function.
     * @example
     *
     * var objects = [
     *   { 'a': 1, 'b': 2, 'c': 3 },
     *   { 'a': 4, 'b': 5, 'c': 6 }
     * ];
     *
     * _.filter(objects, _.matches({ 'a': 4, 'c': 6 }));
     * // => [{ 'a': 4, 'b': 5, 'c': 6 }]
     *
     * // Checking for several possible values
     * _.filter(objects, _.overSome([_.matches({ 'a': 1 }), _.matches({ 'a': 4 })]));
     * // => [{ 'a': 1, 'b': 2, 'c': 3 }, { 'a': 4, 'b': 5, 'c': 6 }]
     */
    function matches(source) {
      return baseMatches(baseClone(source, CLONE_DEEP_FLAG));
    }

    /**
     * Creates a function that performs a partial deep comparison between the
     * value at `path` of a given object to `srcValue`, returning `true` if the
     * object value is equivalent, else `false`.
     *
     * **Note:** Partial comparisons will match empty array and empty object
     * `srcValue` values against any array or object value, respectively. See
     * `_.isEqual` for a list of supported value comparisons.
     *
     * **Note:** Multiple values can be checked by combining several matchers
     * using `_.overSome`
     *
     * @static
     * @memberOf _
     * @since 3.2.0
     * @category Util
     * @param {Array|string} path The path of the property to get.
     * @param {*} srcValue The value to match.
     * @returns {Function} Returns the new spec function.
     * @example
     *
     * var objects = [
     *   { 'a': 1, 'b': 2, 'c': 3 },
     *   { 'a': 4, 'b': 5, 'c': 6 }
     * ];
     *
     * _.find(objects, _.matchesProperty('a', 4));
     * // => { 'a': 4, 'b': 5, 'c': 6 }
     *
     * // Checking for several possible values
     * _.filter(objects, _.overSome([_.matchesProperty('a', 1), _.matchesProperty('a', 4)]));
     * // => [{ 'a': 1, 'b': 2, 'c': 3 }, { 'a': 4, 'b': 5, 'c': 6 }]
     */
    function matchesProperty(path, srcValue) {
      return baseMatchesProperty(path, baseClone(srcValue, CLONE_DEEP_FLAG));
    }

    /**
     * Creates a function that invokes the method at `path` of a given object.
     * Any additional arguments are provided to the invoked method.
     *
     * @static
     * @memberOf _
     * @since 3.7.0
     * @category Util
     * @param {Array|string} path The path of the method to invoke.
     * @param {...*} [args] The arguments to invoke the method with.
     * @returns {Function} Returns the new invoker function.
     * @example
     *
     * var objects = [
     *   { 'a': { 'b': _.constant(2) } },
     *   { 'a': { 'b': _.constant(1) } }
     * ];
     *
     * _.map(objects, _.method('a.b'));
     * // => [2, 1]
     *
     * _.map(objects, _.method(['a', 'b']));
     * // => [2, 1]
     */
    var method = baseRest(function(path, args) {
      return function(object) {
        return baseInvoke(object, path, args);
      };
    });

    /**
     * The opposite of `_.method`; this method creates a function that invokes
     * the method at a given path of `object`. Any additional arguments are
     * provided to the invoked method.
     *
     * @static
     * @memberOf _
     * @since 3.7.0
     * @category Util
     * @param {Object} object The object to query.
     * @param {...*} [args] The arguments to invoke the method with.
     * @returns {Function} Returns the new invoker function.
     * @example
     *
     * var array = _.times(3, _.constant),
     *     object = { 'a': array, 'b': array, 'c': array };
     *
     * _.map(['a[2]', 'c[0]'], _.methodOf(object));
     * // => [2, 0]
     *
     * _.map([['a', '2'], ['c', '0']], _.methodOf(object));
     * // => [2, 0]
     */
    var methodOf = baseRest(function(object, args) {
      return function(path) {
        return baseInvoke(object, path, args);
      };
    });

    /**
     * Adds all own enumerable string keyed function properties of a source
     * object to the destination object. If `object` is a function, then methods
     * are added to its prototype as well.
     *
     * **Note:** Use `_.runInContext` to create a pristine `lodash` function to
     * avoid conflicts caused by modifying the original.
     *
     * @static
     * @since 0.1.0
     * @memberOf _
     * @category Util
     * @param {Function|Object} [object=lodash] The destination object.
     * @param {Object} source The object of functions to add.
     * @param {Object} [options={}] The options object.
     * @param {boolean} [options.chain=true] Specify whether mixins are chainable.
     * @returns {Function|Object} Returns `object`.
     * @example
     *
     * function vowels(string) {
     *   return _.filter(string, function(v) {
     *     return /[aeiou]/i.test(v);
     *   });
     * }
     *
     * _.mixin({ 'vowels': vowels });
     * _.vowels('fred');
     * // => ['e']
     *
     * _('fred').vowels().value();
     * // => ['e']
     *
     * _.mixin({ 'vowels': vowels }, { 'chain': false });
     * _('fred').vowels();
     * // => ['e']
     */
    function mixin(object, source, options) {
      var props = keys(source),
          methodNames = baseFunctions(source, props);

      if (options == null &&
          !(isObject(source) && (methodNames.length || !props.length))) {
        options = source;
        source = object;
        object = this;
        methodNames = baseFunctions(source, keys(source));
      }
      var chain = !(isObject(options) && 'chain' in options) || !!options.chain,
          isFunc = isFunction(object);

      arrayEach(methodNames, function(methodName) {
        var func = source[methodName];
        object[methodName] = func;
        if (isFunc) {
          object.prototype[methodName] = function() {
            var chainAll = this.__chain__;
            if (chain || chainAll) {
              var result = object(this.__wrapped__),
                  actions = result.__actions__ = copyArray(this.__actions__);

              actions.push({ 'func': func, 'args': arguments, 'thisArg': object });
              result.__chain__ = chainAll;
              return result;
            }
            return func.apply(object, arrayPush([this.value()], arguments));
          };
        }
      });

      return object;
    }

    /**
     * Reverts the `_` variable to its previous value and returns a reference to
     * the `lodash` function.
     *
     * @static
     * @since 0.1.0
     * @memberOf _
     * @category Util
     * @returns {Function} Returns the `lodash` function.
     * @example
     *
     * var lodash = _.noConflict();
     */
    function noConflict() {
      if (root._ === this) {
        root._ = oldDash;
      }
      return this;
    }

    /**
     * This method returns `undefined`.
     *
     * @static
     * @memberOf _
     * @since 2.3.0
     * @category Util
     * @example
     *
     * _.times(2, _.noop);
     * // => [undefined, undefined]
     */
    function noop() {
      // No operation performed.
    }

    /**
     * Creates a function that gets the argument at index `n`. If `n` is negative,
     * the nth argument from the end is returned.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Util
     * @param {number} [n=0] The index of the argument to return.
     * @returns {Function} Returns the new pass-thru function.
     * @example
     *
     * var func = _.nthArg(1);
     * func('a', 'b', 'c', 'd');
     * // => 'b'
     *
     * var func = _.nthArg(-2);
     * func('a', 'b', 'c', 'd');
     * // => 'c'
     */
    function nthArg(n) {
      n = toInteger(n);
      return baseRest(function(args) {
        return baseNth(args, n);
      });
    }

    /**
     * Creates a function that invokes `iteratees` with the arguments it receives
     * and returns their results.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Util
     * @param {...(Function|Function[])} [iteratees=[_.identity]]
     *  The iteratees to invoke.
     * @returns {Function} Returns the new function.
     * @example
     *
     * var func = _.over([Math.max, Math.min]);
     *
     * func(1, 2, 3, 4);
     * // => [4, 1]
     */
    var over = createOver(arrayMap);

    /**
     * Creates a function that checks if **all** of the `predicates` return
     * truthy when invoked with the arguments it receives.
     *
     * Following shorthands are possible for providing predicates.
     * Pass an `Object` and it will be used as an parameter for `_.matches` to create the predicate.
     * Pass an `Array` of parameters for `_.matchesProperty` and the predicate will be created using them.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Util
     * @param {...(Function|Function[])} [predicates=[_.identity]]
     *  The predicates to check.
     * @returns {Function} Returns the new function.
     * @example
     *
     * var func = _.overEvery([Boolean, isFinite]);
     *
     * func('1');
     * // => true
     *
     * func(null);
     * // => false
     *
     * func(NaN);
     * // => false
     */
    var overEvery = createOver(arrayEvery);

    /**
     * Creates a function that checks if **any** of the `predicates` return
     * truthy when invoked with the arguments it receives.
     *
     * Following shorthands are possible for providing predicates.
     * Pass an `Object` and it will be used as an parameter for `_.matches` to create the predicate.
     * Pass an `Array` of parameters for `_.matchesProperty` and the predicate will be created using them.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Util
     * @param {...(Function|Function[])} [predicates=[_.identity]]
     *  The predicates to check.
     * @returns {Function} Returns the new function.
     * @example
     *
     * var func = _.overSome([Boolean, isFinite]);
     *
     * func('1');
     * // => true
     *
     * func(null);
     * // => true
     *
     * func(NaN);
     * // => false
     *
     * var matchesFunc = _.overSome([{ 'a': 1 }, { 'a': 2 }])
     * var matchesPropertyFunc = _.overSome([['a', 1], ['a', 2]])
     */
    var overSome = createOver(arraySome);

    /**
     * Creates a function that returns the value at `path` of a given object.
     *
     * @static
     * @memberOf _
     * @since 2.4.0
     * @category Util
     * @param {Array|string} path The path of the property to get.
     * @returns {Function} Returns the new accessor function.
     * @example
     *
     * var objects = [
     *   { 'a': { 'b': 2 } },
     *   { 'a': { 'b': 1 } }
     * ];
     *
     * _.map(objects, _.property('a.b'));
     * // => [2, 1]
     *
     * _.map(_.sortBy(objects, _.property(['a', 'b'])), 'a.b');
     * // => [1, 2]
     */
    function property(path) {
      return isKey(path) ? baseProperty(toKey(path)) : basePropertyDeep(path);
    }

    /**
     * The opposite of `_.property`; this method creates a function that returns
     * the value at a given path of `object`.
     *
     * @static
     * @memberOf _
     * @since 3.0.0
     * @category Util
     * @param {Object} object The object to query.
     * @returns {Function} Returns the new accessor function.
     * @example
     *
     * var array = [0, 1, 2],
     *     object = { 'a': array, 'b': array, 'c': array };
     *
     * _.map(['a[2]', 'c[0]'], _.propertyOf(object));
     * // => [2, 0]
     *
     * _.map([['a', '2'], ['c', '0']], _.propertyOf(object));
     * // => [2, 0]
     */
    function propertyOf(object) {
      return function(path) {
        return object == null ? undefined : baseGet(object, path);
      };
    }

    /**
     * Creates an array of numbers (positive and/or negative) progressing from
     * `start` up to, but not including, `end`. A step of `-1` is used if a negative
     * `start` is specified without an `end` or `step`. If `end` is not specified,
     * it's set to `start` with `start` then set to `0`.
     *
     * **Note:** JavaScript follows the IEEE-754 standard for resolving
     * floating-point values which can produce unexpected results.
     *
     * @static
     * @since 0.1.0
     * @memberOf _
     * @category Util
     * @param {number} [start=0] The start of the range.
     * @param {number} end The end of the range.
     * @param {number} [step=1] The value to increment or decrement by.
     * @returns {Array} Returns the range of numbers.
     * @see _.inRange, _.rangeRight
     * @example
     *
     * _.range(4);
     * // => [0, 1, 2, 3]
     *
     * _.range(-4);
     * // => [0, -1, -2, -3]
     *
     * _.range(1, 5);
     * // => [1, 2, 3, 4]
     *
     * _.range(0, 20, 5);
     * // => [0, 5, 10, 15]
     *
     * _.range(0, -4, -1);
     * // => [0, -1, -2, -3]
     *
     * _.range(1, 4, 0);
     * // => [1, 1, 1]
     *
     * _.range(0);
     * // => []
     */
    var range = createRange();

    /**
     * This method is like `_.range` except that it populates values in
     * descending order.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Util
     * @param {number} [start=0] The start of the range.
     * @param {number} end The end of the range.
     * @param {number} [step=1] The value to increment or decrement by.
     * @returns {Array} Returns the range of numbers.
     * @see _.inRange, _.range
     * @example
     *
     * _.rangeRight(4);
     * // => [3, 2, 1, 0]
     *
     * _.rangeRight(-4);
     * // => [-3, -2, -1, 0]
     *
     * _.rangeRight(1, 5);
     * // => [4, 3, 2, 1]
     *
     * _.rangeRight(0, 20, 5);
     * // => [15, 10, 5, 0]
     *
     * _.rangeRight(0, -4, -1);
     * // => [-3, -2, -1, 0]
     *
     * _.rangeRight(1, 4, 0);
     * // => [1, 1, 1]
     *
     * _.rangeRight(0);
     * // => []
     */
    var rangeRight = createRange(true);

    /**
     * This method returns a new empty array.
     *
     * @static
     * @memberOf _
     * @since 4.13.0
     * @category Util
     * @returns {Array} Returns the new empty array.
     * @example
     *
     * var arrays = _.times(2, _.stubArray);
     *
     * console.log(arrays);
     * // => [[], []]
     *
     * console.log(arrays[0] === arrays[1]);
     * // => false
     */
    function stubArray() {
      return [];
    }

    /**
     * This method returns `false`.
     *
     * @static
     * @memberOf _
     * @since 4.13.0
     * @category Util
     * @returns {boolean} Returns `false`.
     * @example
     *
     * _.times(2, _.stubFalse);
     * // => [false, false]
     */
    function stubFalse() {
      return false;
    }

    /**
     * This method returns a new empty object.
     *
     * @static
     * @memberOf _
     * @since 4.13.0
     * @category Util
     * @returns {Object} Returns the new empty object.
     * @example
     *
     * var objects = _.times(2, _.stubObject);
     *
     * console.log(objects);
     * // => [{}, {}]
     *
     * console.log(objects[0] === objects[1]);
     * // => false
     */
    function stubObject() {
      return {};
    }

    /**
     * This method returns an empty string.
     *
     * @static
     * @memberOf _
     * @since 4.13.0
     * @category Util
     * @returns {string} Returns the empty string.
     * @example
     *
     * _.times(2, _.stubString);
     * // => ['', '']
     */
    function stubString() {
      return '';
    }

    /**
     * This method returns `true`.
     *
     * @static
     * @memberOf _
     * @since 4.13.0
     * @category Util
     * @returns {boolean} Returns `true`.
     * @example
     *
     * _.times(2, _.stubTrue);
     * // => [true, true]
     */
    function stubTrue() {
      return true;
    }

    /**
     * Invokes the iteratee `n` times, returning an array of the results of
     * each invocation. The iteratee is invoked with one argument; (index).
     *
     * @static
     * @since 0.1.0
     * @memberOf _
     * @category Util
     * @param {number} n The number of times to invoke `iteratee`.
     * @param {Function} [iteratee=_.identity] The function invoked per iteration.
     * @returns {Array} Returns the array of results.
     * @example
     *
     * _.times(3, String);
     * // => ['0', '1', '2']
     *
     *  _.times(4, _.constant(0));
     * // => [0, 0, 0, 0]
     */
    function times(n, iteratee) {
      n = toInteger(n);
      if (n < 1 || n > MAX_SAFE_INTEGER) {
        return [];
      }
      var index = MAX_ARRAY_LENGTH,
          length = nativeMin(n, MAX_ARRAY_LENGTH);

      iteratee = getIteratee(iteratee);
      n -= MAX_ARRAY_LENGTH;

      var result = baseTimes(length, iteratee);
      while (++index < n) {
        iteratee(index);
      }
      return result;
    }

    /**
     * Converts `value` to a property path array.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Util
     * @param {*} value The value to convert.
     * @returns {Array} Returns the new property path array.
     * @example
     *
     * _.toPath('a.b.c');
     * // => ['a', 'b', 'c']
     *
     * _.toPath('a[0].b.c');
     * // => ['a', '0', 'b', 'c']
     */
    function toPath(value) {
      if (isArray(value)) {
        return arrayMap(value, toKey);
      }
      return isSymbol(value) ? [value] : copyArray(stringToPath(toString(value)));
    }

    /**
     * Generates a unique ID. If `prefix` is given, the ID is appended to it.
     *
     * @static
     * @since 0.1.0
     * @memberOf _
     * @category Util
     * @param {string} [prefix=''] The value to prefix the ID with.
     * @returns {string} Returns the unique ID.
     * @example
     *
     * _.uniqueId('contact_');
     * // => 'contact_104'
     *
     * _.uniqueId();
     * // => '105'
     */
    function uniqueId(prefix) {
      var id = ++idCounter;
      return toString(prefix) + id;
    }

    /*------------------------------------------------------------------------*/

    /**
     * Adds two numbers.
     *
     * @static
     * @memberOf _
     * @since 3.4.0
     * @category Math
     * @param {number} augend The first number in an addition.
     * @param {number} addend The second number in an addition.
     * @returns {number} Returns the total.
     * @example
     *
     * _.add(6, 4);
     * // => 10
     */
    var add = createMathOperation(function(augend, addend) {
      return augend + addend;
    }, 0);

    /**
     * Computes `number` rounded up to `precision`.
     *
     * @static
     * @memberOf _
     * @since 3.10.0
     * @category Math
     * @param {number} number The number to round up.
     * @param {number} [precision=0] The precision to round up to.
     * @returns {number} Returns the rounded up number.
     * @example
     *
     * _.ceil(4.006);
     * // => 5
     *
     * _.ceil(6.004, 2);
     * // => 6.01
     *
     * _.ceil(6040, -2);
     * // => 6100
     */
    var ceil = createRound('ceil');

    /**
     * Divide two numbers.
     *
     * @static
     * @memberOf _
     * @since 4.7.0
     * @category Math
     * @param {number} dividend The first number in a division.
     * @param {number} divisor The second number in a division.
     * @returns {number} Returns the quotient.
     * @example
     *
     * _.divide(6, 4);
     * // => 1.5
     */
    var divide = createMathOperation(function(dividend, divisor) {
      return dividend / divisor;
    }, 1);

    /**
     * Computes `number` rounded down to `precision`.
     *
     * @static
     * @memberOf _
     * @since 3.10.0
     * @category Math
     * @param {number} number The number to round down.
     * @param {number} [precision=0] The precision to round down to.
     * @returns {number} Returns the rounded down number.
     * @example
     *
     * _.floor(4.006);
     * // => 4
     *
     * _.floor(0.046, 2);
     * // => 0.04
     *
     * _.floor(4060, -2);
     * // => 4000
     */
    var floor = createRound('floor');

    /**
     * Computes the maximum value of `array`. If `array` is empty or falsey,
     * `undefined` is returned.
     *
     * @static
     * @since 0.1.0
     * @memberOf _
     * @category Math
     * @param {Array} array The array to iterate over.
     * @returns {*} Returns the maximum value.
     * @example
     *
     * _.max([4, 2, 8, 6]);
     * // => 8
     *
     * _.max([]);
     * // => undefined
     */
    function max(array) {
      return (array && array.length)
        ? baseExtremum(array, identity, baseGt)
        : undefined;
    }

    /**
     * This method is like `_.max` except that it accepts `iteratee` which is
     * invoked for each element in `array` to generate the criterion by which
     * the value is ranked. The iteratee is invoked with one argument: (value).
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Math
     * @param {Array} array The array to iterate over.
     * @param {Function} [iteratee=_.identity] The iteratee invoked per element.
     * @returns {*} Returns the maximum value.
     * @example
     *
     * var objects = [{ 'n': 1 }, { 'n': 2 }];
     *
     * _.maxBy(objects, function(o) { return o.n; });
     * // => { 'n': 2 }
     *
     * // The `_.property` iteratee shorthand.
     * _.maxBy(objects, 'n');
     * // => { 'n': 2 }
     */
    function maxBy(array, iteratee) {
      return (array && array.length)
        ? baseExtremum(array, getIteratee(iteratee, 2), baseGt)
        : undefined;
    }

    /**
     * Computes the mean of the values in `array`.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Math
     * @param {Array} array The array to iterate over.
     * @returns {number} Returns the mean.
     * @example
     *
     * _.mean([4, 2, 8, 6]);
     * // => 5
     */
    function mean(array) {
      return baseMean(array, identity);
    }

    /**
     * This method is like `_.mean` except that it accepts `iteratee` which is
     * invoked for each element in `array` to generate the value to be averaged.
     * The iteratee is invoked with one argument: (value).
     *
     * @static
     * @memberOf _
     * @since 4.7.0
     * @category Math
     * @param {Array} array The array to iterate over.
     * @param {Function} [iteratee=_.identity] The iteratee invoked per element.
     * @returns {number} Returns the mean.
     * @example
     *
     * var objects = [{ 'n': 4 }, { 'n': 2 }, { 'n': 8 }, { 'n': 6 }];
     *
     * _.meanBy(objects, function(o) { return o.n; });
     * // => 5
     *
     * // The `_.property` iteratee shorthand.
     * _.meanBy(objects, 'n');
     * // => 5
     */
    function meanBy(array, iteratee) {
      return baseMean(array, getIteratee(iteratee, 2));
    }

    /**
     * Computes the minimum value of `array`. If `array` is empty or falsey,
     * `undefined` is returned.
     *
     * @static
     * @since 0.1.0
     * @memberOf _
     * @category Math
     * @param {Array} array The array to iterate over.
     * @returns {*} Returns the minimum value.
     * @example
     *
     * _.min([4, 2, 8, 6]);
     * // => 2
     *
     * _.min([]);
     * // => undefined
     */
    function min(array) {
      return (array && array.length)
        ? baseExtremum(array, identity, baseLt)
        : undefined;
    }

    /**
     * This method is like `_.min` except that it accepts `iteratee` which is
     * invoked for each element in `array` to generate the criterion by which
     * the value is ranked. The iteratee is invoked with one argument: (value).
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Math
     * @param {Array} array The array to iterate over.
     * @param {Function} [iteratee=_.identity] The iteratee invoked per element.
     * @returns {*} Returns the minimum value.
     * @example
     *
     * var objects = [{ 'n': 1 }, { 'n': 2 }];
     *
     * _.minBy(objects, function(o) { return o.n; });
     * // => { 'n': 1 }
     *
     * // The `_.property` iteratee shorthand.
     * _.minBy(objects, 'n');
     * // => { 'n': 1 }
     */
    function minBy(array, iteratee) {
      return (array && array.length)
        ? baseExtremum(array, getIteratee(iteratee, 2), baseLt)
        : undefined;
    }

    /**
     * Multiply two numbers.
     *
     * @static
     * @memberOf _
     * @since 4.7.0
     * @category Math
     * @param {number} multiplier The first number in a multiplication.
     * @param {number} multiplicand The second number in a multiplication.
     * @returns {number} Returns the product.
     * @example
     *
     * _.multiply(6, 4);
     * // => 24
     */
    var multiply = createMathOperation(function(multiplier, multiplicand) {
      return multiplier * multiplicand;
    }, 1);

    /**
     * Computes `number` rounded to `precision`.
     *
     * @static
     * @memberOf _
     * @since 3.10.0
     * @category Math
     * @param {number} number The number to round.
     * @param {number} [precision=0] The precision to round to.
     * @returns {number} Returns the rounded number.
     * @example
     *
     * _.round(4.006);
     * // => 4
     *
     * _.round(4.006, 2);
     * // => 4.01
     *
     * _.round(4060, -2);
     * // => 4100
     */
    var round = createRound('round');

    /**
     * Subtract two numbers.
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Math
     * @param {number} minuend The first number in a subtraction.
     * @param {number} subtrahend The second number in a subtraction.
     * @returns {number} Returns the difference.
     * @example
     *
     * _.subtract(6, 4);
     * // => 2
     */
    var subtract = createMathOperation(function(minuend, subtrahend) {
      return minuend - subtrahend;
    }, 0);

    /**
     * Computes the sum of the values in `array`.
     *
     * @static
     * @memberOf _
     * @since 3.4.0
     * @category Math
     * @param {Array} array The array to iterate over.
     * @returns {number} Returns the sum.
     * @example
     *
     * _.sum([4, 2, 8, 6]);
     * // => 20
     */
    function sum(array) {
      return (array && array.length)
        ? baseSum(array, identity)
        : 0;
    }

    /**
     * This method is like `_.sum` except that it accepts `iteratee` which is
     * invoked for each element in `array` to generate the value to be summed.
     * The iteratee is invoked with one argument: (value).
     *
     * @static
     * @memberOf _
     * @since 4.0.0
     * @category Math
     * @param {Array} array The array to iterate over.
     * @param {Function} [iteratee=_.identity] The iteratee invoked per element.
     * @returns {number} Returns the sum.
     * @example
     *
     * var objects = [{ 'n': 4 }, { 'n': 2 }, { 'n': 8 }, { 'n': 6 }];
     *
     * _.sumBy(objects, function(o) { return o.n; });
     * // => 20
     *
     * // The `_.property` iteratee shorthand.
     * _.sumBy(objects, 'n');
     * // => 20
     */
    function sumBy(array, iteratee) {
      return (array && array.length)
        ? baseSum(array, getIteratee(iteratee, 2))
        : 0;
    }

    /*------------------------------------------------------------------------*/

    // Add methods that return wrapped values in chain sequences.
    lodash.after = after;
    lodash.ary = ary;
    lodash.assign = assign;
    lodash.assignIn = assignIn;
    lodash.assignInWith = assignInWith;
    lodash.assignWith = assignWith;
    lodash.at = at;
    lodash.before = before;
    lodash.bind = bind;
    lodash.bindAll = bindAll;
    lodash.bindKey = bindKey;
    lodash.castArray = castArray;
    lodash.chain = chain;
    lodash.chunk = chunk;
    lodash.compact = compact;
    lodash.concat = concat;
    lodash.cond = cond;
    lodash.conforms = conforms;
    lodash.constant = constant;
    lodash.countBy = countBy;
    lodash.create = create;
    lodash.curry = curry;
    lodash.curryRight = curryRight;
    lodash.debounce = debounce;
    lodash.defaults = defaults;
    lodash.defaultsDeep = defaultsDeep;
    lodash.defer = defer;
    lodash.delay = delay;
    lodash.difference = difference;
    lodash.differenceBy = differenceBy;
    lodash.differenceWith = differenceWith;
    lodash.drop = drop;
    lodash.dropRight = dropRight;
    lodash.dropRightWhile = dropRightWhile;
    lodash.dropWhile = dropWhile;
    lodash.fill = fill;
    lodash.filter = filter;
    lodash.flatMap = flatMap;
    lodash.flatMapDeep = flatMapDeep;
    lodash.flatMapDepth = flatMapDepth;
    lodash.flatten = flatten;
    lodash.flattenDeep = flattenDeep;
    lodash.flattenDepth = flattenDepth;
    lodash.flip = flip;
    lodash.flow = flow;
    lodash.flowRight = flowRight;
    lodash.fromPairs = fromPairs;
    lodash.functions = functions;
    lodash.functionsIn = functionsIn;
    lodash.groupBy = groupBy;
    lodash.initial = initial;
    lodash.intersection = intersection;
    lodash.intersectionBy = intersectionBy;
    lodash.intersectionWith = intersectionWith;
    lodash.invert = invert;
    lodash.invertBy = invertBy;
    lodash.invokeMap = invokeMap;
    lodash.iteratee = iteratee;
    lodash.keyBy = keyBy;
    lodash.keys = keys;
    lodash.keysIn = keysIn;
    lodash.map = map;
    lodash.mapKeys = mapKeys;
    lodash.mapValues = mapValues;
    lodash.matches = matches;
    lodash.matchesProperty = matchesProperty;
    lodash.memoize = memoize;
    lodash.merge = merge;
    lodash.mergeWith = mergeWith;
    lodash.method = method;
    lodash.methodOf = methodOf;
    lodash.mixin = mixin;
    lodash.negate = negate;
    lodash.nthArg = nthArg;
    lodash.omit = omit;
    lodash.omitBy = omitBy;
    lodash.once = once;
    lodash.orderBy = orderBy;
    lodash.over = over;
    lodash.overArgs = overArgs;
    lodash.overEvery = overEvery;
    lodash.overSome = overSome;
    lodash.partial = partial;
    lodash.partialRight = partialRight;
    lodash.partition = partition;
    lodash.pick = pick;
    lodash.pickBy = pickBy;
    lodash.property = property;
    lodash.propertyOf = propertyOf;
    lodash.pull = pull;
    lodash.pullAll = pullAll;
    lodash.pullAllBy = pullAllBy;
    lodash.pullAllWith = pullAllWith;
    lodash.pullAt = pullAt;
    lodash.range = range;
    lodash.rangeRight = rangeRight;
    lodash.rearg = rearg;
    lodash.reject = reject;
    lodash.remove = remove;
    lodash.rest = rest;
    lodash.reverse = reverse;
    lodash.sampleSize = sampleSize;
    lodash.set = set;
    lodash.setWith = setWith;
    lodash.shuffle = shuffle;
    lodash.slice = slice;
    lodash.sortBy = sortBy;
    lodash.sortedUniq = sortedUniq;
    lodash.sortedUniqBy = sortedUniqBy;
    lodash.split = split;
    lodash.spread = spread;
    lodash.tail = tail;
    lodash.take = take;
    lodash.takeRight = takeRight;
    lodash.takeRightWhile = takeRightWhile;
    lodash.takeWhile = takeWhile;
    lodash.tap = tap;
    lodash.throttle = throttle;
    lodash.thru = thru;
    lodash.toArray = toArray;
    lodash.toPairs = toPairs;
    lodash.toPairsIn = toPairsIn;
    lodash.toPath = toPath;
    lodash.toPlainObject = toPlainObject;
    lodash.transform = transform;
    lodash.unary = unary;
    lodash.union = union;
    lodash.unionBy = unionBy;
    lodash.unionWith = unionWith;
    lodash.uniq = uniq;
    lodash.uniqBy = uniqBy;
    lodash.uniqWith = uniqWith;
    lodash.unset = unset;
    lodash.unzip = unzip;
    lodash.unzipWith = unzipWith;
    lodash.update = update;
    lodash.updateWith = updateWith;
    lodash.values = values;
    lodash.valuesIn = valuesIn;
    lodash.without = without;
    lodash.words = words;
    lodash.wrap = wrap;
    lodash.xor = xor;
    lodash.xorBy = xorBy;
    lodash.xorWith = xorWith;
    lodash.zip = zip;
    lodash.zipObject = zipObject;
    lodash.zipObjectDeep = zipObjectDeep;
    lodash.zipWith = zipWith;

    // Add aliases.
    lodash.entries = toPairs;
    lodash.entriesIn = toPairsIn;
    lodash.extend = assignIn;
    lodash.extendWith = assignInWith;

    // Add methods to `lodash.prototype`.
    mixin(lodash, lodash);

    /*------------------------------------------------------------------------*/

    // Add methods that return unwrapped values in chain sequences.
    lodash.add = add;
    lodash.attempt = attempt;
    lodash.camelCase = camelCase;
    lodash.capitalize = capitalize;
    lodash.ceil = ceil;
    lodash.clamp = clamp;
    lodash.clone = clone;
    lodash.cloneDeep = cloneDeep;
    lodash.cloneDeepWith = cloneDeepWith;
    lodash.cloneWith = cloneWith;
    lodash.conformsTo = conformsTo;
    lodash.deburr = deburr;
    lodash.defaultTo = defaultTo;
    lodash.divide = divide;
    lodash.endsWith = endsWith;
    lodash.eq = eq;
    lodash.escape = escape;
    lodash.escapeRegExp = escapeRegExp;
    lodash.every = every;
    lodash.find = find;
    lodash.findIndex = findIndex;
    lodash.findKey = findKey;
    lodash.findLast = findLast;
    lodash.findLastIndex = findLastIndex;
    lodash.findLastKey = findLastKey;
    lodash.floor = floor;
    lodash.forEach = forEach;
    lodash.forEachRight = forEachRight;
    lodash.forIn = forIn;
    lodash.forInRight = forInRight;
    lodash.forOwn = forOwn;
    lodash.forOwnRight = forOwnRight;
    lodash.get = get;
    lodash.gt = gt;
    lodash.gte = gte;
    lodash.has = has;
    lodash.hasIn = hasIn;
    lodash.head = head;
    lodash.identity = identity;
    lodash.includes = includes;
    lodash.indexOf = indexOf;
    lodash.inRange = inRange;
    lodash.invoke = invoke;
    lodash.isArguments = isArguments;
    lodash.isArray = isArray;
    lodash.isArrayBuffer = isArrayBuffer;
    lodash.isArrayLike = isArrayLike;
    lodash.isArrayLikeObject = isArrayLikeObject;
    lodash.isBoolean = isBoolean;
    lodash.isBuffer = isBuffer;
    lodash.isDate = isDate;
    lodash.isElement = isElement;
    lodash.isEmpty = isEmpty;
    lodash.isEqual = isEqual;
    lodash.isEqualWith = isEqualWith;
    lodash.isError = isError;
    lodash.isFinite = isFinite;
    lodash.isFunction = isFunction;
    lodash.isInteger = isInteger;
    lodash.isLength = isLength;
    lodash.isMap = isMap;
    lodash.isMatch = isMatch;
    lodash.isMatchWith = isMatchWith;
    lodash.isNaN = isNaN;
    lodash.isNative = isNative;
    lodash.isNil = isNil;
    lodash.isNull = isNull;
    lodash.isNumber = isNumber;
    lodash.isObject = isObject;
    lodash.isObjectLike = isObjectLike;
    lodash.isPlainObject = isPlainObject;
    lodash.isRegExp = isRegExp;
    lodash.isSafeInteger = isSafeInteger;
    lodash.isSet = isSet;
    lodash.isString = isString;
    lodash.isSymbol = isSymbol;
    lodash.isTypedArray = isTypedArray;
    lodash.isUndefined = isUndefined;
    lodash.isWeakMap = isWeakMap;
    lodash.isWeakSet = isWeakSet;
    lodash.join = join;
    lodash.kebabCase = kebabCase;
    lodash.last = last;
    lodash.lastIndexOf = lastIndexOf;
    lodash.lowerCase = lowerCase;
    lodash.lowerFirst = lowerFirst;
    lodash.lt = lt;
    lodash.lte = lte;
    lodash.max = max;
    lodash.maxBy = maxBy;
    lodash.mean = mean;
    lodash.meanBy = meanBy;
    lodash.min = min;
    lodash.minBy = minBy;
    lodash.stubArray = stubArray;
    lodash.stubFalse = stubFalse;
    lodash.stubObject = stubObject;
    lodash.stubString = stubString;
    lodash.stubTrue = stubTrue;
    lodash.multiply = multiply;
    lodash.nth = nth;
    lodash.noConflict = noConflict;
    lodash.noop = noop;
    lodash.now = now;
    lodash.pad = pad;
    lodash.padEnd = padEnd;
    lodash.padStart = padStart;
    lodash.parseInt = parseInt;
    lodash.random = random;
    lodash.reduce = reduce;
    lodash.reduceRight = reduceRight;
    lodash.repeat = repeat;
    lodash.replace = replace;
    lodash.result = result;
    lodash.round = round;
    lodash.runInContext = runInContext;
    lodash.sample = sample;
    lodash.size = size;
    lodash.snakeCase = snakeCase;
    lodash.some = some;
    lodash.sortedIndex = sortedIndex;
    lodash.sortedIndexBy = sortedIndexBy;
    lodash.sortedIndexOf = sortedIndexOf;
    lodash.sortedLastIndex = sortedLastIndex;
    lodash.sortedLastIndexBy = sortedLastIndexBy;
    lodash.sortedLastIndexOf = sortedLastIndexOf;
    lodash.startCase = startCase;
    lodash.startsWith = startsWith;
    lodash.subtract = subtract;
    lodash.sum = sum;
    lodash.sumBy = sumBy;
    lodash.template = template;
    lodash.times = times;
    lodash.toFinite = toFinite;
    lodash.toInteger = toInteger;
    lodash.toLength = toLength;
    lodash.toLower = toLower;
    lodash.toNumber = toNumber;
    lodash.toSafeInteger = toSafeInteger;
    lodash.toString = toString;
    lodash.toUpper = toUpper;
    lodash.trim = trim;
    lodash.trimEnd = trimEnd;
    lodash.trimStart = trimStart;
    lodash.truncate = truncate;
    lodash.unescape = unescape;
    lodash.uniqueId = uniqueId;
    lodash.upperCase = upperCase;
    lodash.upperFirst = upperFirst;

    // Add aliases.
    lodash.each = forEach;
    lodash.eachRight = forEachRight;
    lodash.first = head;

    mixin(lodash, (function() {
      var source = {};
      baseForOwn(lodash, function(func, methodName) {
        if (!hasOwnProperty.call(lodash.prototype, methodName)) {
          source[methodName] = func;
        }
      });
      return source;
    }()), { 'chain': false });

    /*------------------------------------------------------------------------*/

    /**
     * The semantic version number.
     *
     * @static
     * @memberOf _
     * @type {string}
     */
    lodash.VERSION = VERSION;

    // Assign default placeholders.
    arrayEach(['bind', 'bindKey', 'curry', 'curryRight', 'partial', 'partialRight'], function(methodName) {
      lodash[methodName].placeholder = lodash;
    });

    // Add `LazyWrapper` methods for `_.drop` and `_.take` variants.
    arrayEach(['drop', 'take'], function(methodName, index) {
      LazyWrapper.prototype[methodName] = function(n) {
        n = n === undefined ? 1 : nativeMax(toInteger(n), 0);

        var result = (this.__filtered__ && !index)
          ? new LazyWrapper(this)
          : this.clone();

        if (result.__filtered__) {
          result.__takeCount__ = nativeMin(n, result.__takeCount__);
        } else {
          result.__views__.push({
            'size': nativeMin(n, MAX_ARRAY_LENGTH),
            'type': methodName + (result.__dir__ < 0 ? 'Right' : '')
          });
        }
        return result;
      };

      LazyWrapper.prototype[methodName + 'Right'] = function(n) {
        return this.reverse()[methodName](n).reverse();
      };
    });

    // Add `LazyWrapper` methods that accept an `iteratee` value.
    arrayEach(['filter', 'map', 'takeWhile'], function(methodName, index) {
      var type = index + 1,
          isFilter = type == LAZY_FILTER_FLAG || type == LAZY_WHILE_FLAG;

      LazyWrapper.prototype[methodName] = function(iteratee) {
        var result = this.clone();
        result.__iteratees__.push({
          'iteratee': getIteratee(iteratee, 3),
          'type': type
        });
        result.__filtered__ = result.__filtered__ || isFilter;
        return result;
      };
    });

    // Add `LazyWrapper` methods for `_.head` and `_.last`.
    arrayEach(['head', 'last'], function(methodName, index) {
      var takeName = 'take' + (index ? 'Right' : '');

      LazyWrapper.prototype[methodName] = function() {
        return this[takeName](1).value()[0];
      };
    });

    // Add `LazyWrapper` methods for `_.initial` and `_.tail`.
    arrayEach(['initial', 'tail'], function(methodName, index) {
      var dropName = 'drop' + (index ? '' : 'Right');

      LazyWrapper.prototype[methodName] = function() {
        return this.__filtered__ ? new LazyWrapper(this) : this[dropName](1);
      };
    });

    LazyWrapper.prototype.compact = function() {
      return this.filter(identity);
    };

    LazyWrapper.prototype.find = function(predicate) {
      return this.filter(predicate).head();
    };

    LazyWrapper.prototype.findLast = function(predicate) {
      return this.reverse().find(predicate);
    };

    LazyWrapper.prototype.invokeMap = baseRest(function(path, args) {
      if (typeof path == 'function') {
        return new LazyWrapper(this);
      }
      return this.map(function(value) {
        return baseInvoke(value, path, args);
      });
    });

    LazyWrapper.prototype.reject = function(predicate) {
      return this.filter(negate(getIteratee(predicate)));
    };

    LazyWrapper.prototype.slice = function(start, end) {
      start = toInteger(start);

      var result = this;
      if (result.__filtered__ && (start > 0 || end < 0)) {
        return new LazyWrapper(result);
      }
      if (start < 0) {
        result = result.takeRight(-start);
      } else if (start) {
        result = result.drop(start);
      }
      if (end !== undefined) {
        end = toInteger(end);
        result = end < 0 ? result.dropRight(-end) : result.take(end - start);
      }
      return result;
    };

    LazyWrapper.prototype.takeRightWhile = function(predicate) {
      return this.reverse().takeWhile(predicate).reverse();
    };

    LazyWrapper.prototype.toArray = function() {
      return this.take(MAX_ARRAY_LENGTH);
    };

    // Add `LazyWrapper` methods to `lodash.prototype`.
    baseForOwn(LazyWrapper.prototype, function(func, methodName) {
      var checkIteratee = /^(?:filter|find|map|reject)|While$/.test(methodName),
          isTaker = /^(?:head|last)$/.test(methodName),
          lodashFunc = lodash[isTaker ? ('take' + (methodName == 'last' ? 'Right' : '')) : methodName],
          retUnwrapped = isTaker || /^find/.test(methodName);

      if (!lodashFunc) {
        return;
      }
      lodash.prototype[methodName] = function() {
        var value = this.__wrapped__,
            args = isTaker ? [1] : arguments,
            isLazy = value instanceof LazyWrapper,
            iteratee = args[0],
            useLazy = isLazy || isArray(value);

        var interceptor = function(value) {
          var result = lodashFunc.apply(lodash, arrayPush([value], args));
          return (isTaker && chainAll) ? result[0] : result;
        };

        if (useLazy && checkIteratee && typeof iteratee == 'function' && iteratee.length != 1) {
          // Avoid lazy use if the iteratee has a "length" value other than `1`.
          isLazy = useLazy = false;
        }
        var chainAll = this.__chain__,
            isHybrid = !!this.__actions__.length,
            isUnwrapped = retUnwrapped && !chainAll,
            onlyLazy = isLazy && !isHybrid;

        if (!retUnwrapped && useLazy) {
          value = onlyLazy ? value : new LazyWrapper(this);
          var result = func.apply(value, args);
          result.__actions__.push({ 'func': thru, 'args': [interceptor], 'thisArg': undefined });
          return new LodashWrapper(result, chainAll);
        }
        if (isUnwrapped && onlyLazy) {
          return func.apply(this, args);
        }
        result = this.thru(interceptor);
        return isUnwrapped ? (isTaker ? result.value()[0] : result.value()) : result;
      };
    });

    // Add `Array` methods to `lodash.prototype`.
    arrayEach(['pop', 'push', 'shift', 'sort', 'splice', 'unshift'], function(methodName) {
      var func = arrayProto[methodName],
          chainName = /^(?:push|sort|unshift)$/.test(methodName) ? 'tap' : 'thru',
          retUnwrapped = /^(?:pop|shift)$/.test(methodName);

      lodash.prototype[methodName] = function() {
        var args = arguments;
        if (retUnwrapped && !this.__chain__) {
          var value = this.value();
          return func.apply(isArray(value) ? value : [], args);
        }
        return this[chainName](function(value) {
          return func.apply(isArray(value) ? value : [], args);
        });
      };
    });

    // Map minified method names to their real names.
    baseForOwn(LazyWrapper.prototype, function(func, methodName) {
      var lodashFunc = lodash[methodName];
      if (lodashFunc) {
        var key = lodashFunc.name + '';
        if (!hasOwnProperty.call(realNames, key)) {
          realNames[key] = [];
        }
        realNames[key].push({ 'name': methodName, 'func': lodashFunc });
      }
    });

    realNames[createHybrid(undefined, WRAP_BIND_KEY_FLAG).name] = [{
      'name': 'wrapper',
      'func': undefined
    }];

    // Add methods to `LazyWrapper`.
    LazyWrapper.prototype.clone = lazyClone;
    LazyWrapper.prototype.reverse = lazyReverse;
    LazyWrapper.prototype.value = lazyValue;

    // Add chain sequence methods to the `lodash` wrapper.
    lodash.prototype.at = wrapperAt;
    lodash.prototype.chain = wrapperChain;
    lodash.prototype.commit = wrapperCommit;
    lodash.prototype.next = wrapperNext;
    lodash.prototype.plant = wrapperPlant;
    lodash.prototype.reverse = wrapperReverse;
    lodash.prototype.toJSON = lodash.prototype.valueOf = lodash.prototype.value = wrapperValue;

    // Add lazy aliases.
    lodash.prototype.first = lodash.prototype.head;

    if (symIterator) {
      lodash.prototype[symIterator] = wrapperToIterator;
    }
    return lodash;
  });

  /*--------------------------------------------------------------------------*/

  // Export lodash.
  var _ = runInContext();

  // Some AMD build optimizers, like r.js, check for condition patterns like:
  if (typeof define == 'function' && typeof define.amd == 'object' && define.amd) {
    // Expose Lodash on the global object to prevent errors when Lodash is
    // loaded by a script tag in the presence of an AMD loader.
    // See http://requirejs.org/docs/errors.html#mismatch for more details.
    // Use `_.noConflict` to remove Lodash from the global object.
    root._ = _;

    // Define as an anonymous module so, through path mapping, it can be
    // referenced as the "underscore" module.
    define(function() {
      return _;
    });
  }
  // Check for `exports` after `define` in case a build optimizer adds it.
  else if (freeModule) {
    // Export for Node.js.
    (freeModule.exports = _)._ = _;
    // Export for CommonJS support.
    freeExports._ = _;
  }
  else {
    // Export to the global object.
    root._ = _;
  }
}.call(this));

}).call(this,typeof global !== "undefined" ? global : typeof self !== "undefined" ? self : typeof window !== "undefined" ? window : {})
},{}],11:[function(require,module,exports){
/**
 * The MIT License (MIT)
 * Copyright (c) 2017-present Dmitry Soshnikov <dmitry.soshnikov@gmail.com>
 */

'use strict';

var compatTransforms = require('./transforms');
var _transform = require('../transform');

module.exports = {
  /**
   * Translates a regexp in new syntax to equivalent regexp in old syntax.
   *
   * @param string|RegExp|AST - regexp
   * @param Array transformsWhitelist - names of the transforms to apply
   */
  transform: function transform(regexp) {
    var transformsWhitelist = arguments.length > 1 && arguments[1] !== undefined ? arguments[1] : [];

    var transformToApply = transformsWhitelist.length > 0 ? transformsWhitelist : Object.keys(compatTransforms);

    var result = void 0;

    // Collect extra data per transform.
    var extra = {};

    transformToApply.forEach(function (transformName) {

      if (!compatTransforms.hasOwnProperty(transformName)) {
        throw new Error('Unknown compat-transform: ' + transformName + '. ' + 'Available transforms are: ' + Object.keys(compatTransforms).join(', '));
      }

      var handler = compatTransforms[transformName];

      result = _transform.transform(regexp, handler);
      regexp = result.getAST();

      // Collect `extra` transform result.
      if (typeof handler.getExtra === 'function') {
        extra[transformName] = handler.getExtra();
      }
    });

    // Set the final extras for all transforms.
    result.setExtra(extra);

    return result;
  }
};
},{"../transform":49,"./transforms":16}],12:[function(require,module,exports){
/**
 * The MIT License (MIT)
 * Copyright (c) 2017-present Dmitry Soshnikov <dmitry.soshnikov@gmail.com>
 */

'use strict';

/**
 * The `RegExpTree` class provides runtime support for `compat-transpiler`
 * module from `regexp-tree`.
 *
 * E.g. it tracks names of the capturing groups, in order to access the
 * names on the matched result.
 *
 * It's a thin-wrapper on top of original regexp.
 */

var _createClass = function () { function defineProperties(target, props) { for (var i = 0; i < props.length; i++) { var descriptor = props[i]; descriptor.enumerable = descriptor.enumerable || false; descriptor.configurable = true; if ("value" in descriptor) descriptor.writable = true; Object.defineProperty(target, descriptor.key, descriptor); } } return function (Constructor, protoProps, staticProps) { if (protoProps) defineProperties(Constructor.prototype, protoProps); if (staticProps) defineProperties(Constructor, staticProps); return Constructor; }; }();

function _classCallCheck(instance, Constructor) { if (!(instance instanceof Constructor)) { throw new TypeError("Cannot call a class as a function"); } }

var RegExpTree = function () {
  /**
   * Initializes a `RegExpTree` instance.
   *
   * @param RegExp - a regular expression
   *
   * @param Object state:
   *
   *   An extra state which may store any related to transformation
   *   data, for example, names of the groups.
   *
   *   - flags - original flags
   *   - groups - names of the groups, and their indices
   *   - source - original source
   */
  function RegExpTree(re, _ref) {
    var flags = _ref.flags,
        groups = _ref.groups,
        source = _ref.source;

    _classCallCheck(this, RegExpTree);

    this._re = re;
    this._groups = groups;

    // Original props.
    this.flags = flags;
    this.source = source || re.source;
    this.dotAll = flags.includes('s');

    // Inherited directly from `re`.
    this.global = re.global;
    this.ignoreCase = re.ignoreCase;
    this.multiline = re.multiline;
    this.sticky = re.sticky;
    this.unicode = re.unicode;
  }

  /**
   * Facade wrapper for RegExp `test` method.
   */


  _createClass(RegExpTree, [{
    key: 'test',
    value: function test(string) {
      return this._re.test(string);
    }

    /**
     * Facade wrapper for RegExp `compile` method.
     */

  }, {
    key: 'compile',
    value: function compile(string) {
      return this._re.compile(string);
    }

    /**
     * Facade wrapper for RegExp `toString` method.
     */

  }, {
    key: 'toString',
    value: function toString() {
      if (!this._toStringResult) {
        this._toStringResult = '/' + this.source + '/' + this.flags;
      }
      return this._toStringResult;
    }

    /**
     * Facade wrapper for RegExp `exec` method.
     */

  }, {
    key: 'exec',
    value: function exec(string) {
      var result = this._re.exec(string);

      if (!this._groups || !result) {
        return result;
      }

      result.groups = {};

      for (var group in this._groups) {
        var groupNumber = this._groups[group];
        result.groups[group] = result[groupNumber];
      }

      return result;
    }
  }]);

  return RegExpTree;
}();

module.exports = {
  RegExpTree: RegExpTree
};
},{}],13:[function(require,module,exports){
/**
 * The MIT License (MIT)
 * Copyright (c) 2017-present Dmitry Soshnikov <dmitry.soshnikov@gmail.com>
 */

'use strict';

/**
 * A regexp-tree plugin to translate `/./s` to `/[\0-\uFFFF]/`.
 */

module.exports = {

  // Whether `u` flag present. In which case we transform to
  // \u{10FFFF} instead of \uFFFF.
  _hasUFlag: false,

  // Only run this plugin if we have `s` flag.
  shouldRun: function shouldRun(ast) {
    var shouldRun = ast.flags.includes('s');

    if (!shouldRun) {
      return false;
    }

    // Strip the `s` flag.
    ast.flags = ast.flags.replace('s', '');

    // Whether we have also `u`.
    this._hasUFlag = ast.flags.includes('u');

    return true;
  },
  Char: function Char(path) {
    var node = path.node;


    if (node.kind !== 'meta' || node.value !== '.') {
      return;
    }

    var toValue = '\\uFFFF';
    var toSymbol = '\uFFFF';

    if (this._hasUFlag) {
      toValue = '\\u{10FFFF}';
      toSymbol = '\uDBFF\uDFFF';
    }

    path.replace({
      type: 'CharacterClass',
      expressions: [{
        type: 'ClassRange',
        from: {
          type: 'Char',
          value: '\\0',
          kind: 'decimal',
          symbol: '\0'
        },
        to: {
          type: 'Char',
          value: toValue,
          kind: 'unicode',
          symbol: toSymbol
        }
      }]
    });
  }
};
},{}],14:[function(require,module,exports){
/**
 * The MIT License (MIT)
 * Copyright (c) 2017-present Dmitry Soshnikov <dmitry.soshnikov@gmail.com>
 */

'use strict';

/**
 * A regexp-tree plugin to translate `/(?<name>a)\k<name>/` to `/(a)\1/`.
 */

module.exports = {
  // To track the names of the groups, and return them
  // in the transform result state.
  //
  // A map from name to number: {foo: 2, bar: 4}
  _groupNames: {},

  /**
   * Initialises the trasnform.
   */
  init: function init() {
    this._groupNames = {};
  },


  /**
   * Returns extra state, which eventually is returned to
   */
  getExtra: function getExtra() {
    return this._groupNames;
  },
  Group: function Group(path) {
    var node = path.node;


    if (!node.name) {
      return;
    }

    // Record group name.
    this._groupNames[node.name] = node.number;

    delete node.name;
    delete node.nameRaw;
  },
  Backreference: function Backreference(path) {
    var node = path.node;


    if (node.kind !== 'name') {
      return;
    }

    node.kind = 'number';
    node.reference = node.number;
    delete node.referenceRaw;
  }
};
},{}],15:[function(require,module,exports){
/**
 * The MIT License (MIT)
 * Copyright (c) 2017-present Dmitry Soshnikov <dmitry.soshnikov@gmail.com>
 */

'use strict';

/**
 * A regexp-tree plugin to remove `x` flag `/foo/x` to `/foo/`.
 *
 * Note: other features of `x` flags (whitespace, comments) are
 * already removed at parsing stage.
 */

module.exports = {
  RegExp: function RegExp(_ref) {
    var node = _ref.node;

    if (node.flags.includes('x')) {
      node.flags = node.flags.replace('x', '');
    }
  }
};
},{}],16:[function(require,module,exports){
/**
 * The MIT License (MIT)
 * Copyright (c) 2017-present Dmitry Soshnikov <dmitry.soshnikov@gmail.com>
 */

'use strict';

module.exports = {
  // "dotAll" `s` flag
  dotAll: require('./compat-dotall-s-transform'),

  // Named capturing groups.
  namedCapturingGroups: require('./compat-named-capturing-groups-transform'),

  // `x` flag
  xFlag: require('./compat-x-flag-transform')
};
},{"./compat-dotall-s-transform":13,"./compat-named-capturing-groups-transform":14,"./compat-x-flag-transform":15}],17:[function(require,module,exports){
/**
 * The MIT License (MIT)
 * Copyright (c) 2017-present Dmitry Soshnikov <dmitry.soshnikov@gmail.com>
 */

'use strict';

/**
 * Helper `gen` function calls node type handler.
 */

function gen(node) {
  return node ? generator[node.type](node) : '';
}

/**
 * AST handler.
 */
var generator = {
  RegExp: function RegExp(node) {
    return '/' + gen(node.body) + '/' + node.flags;
  },
  Alternative: function Alternative(node) {
    return (node.expressions || []).map(gen).join('');
  },
  Disjunction: function Disjunction(node) {
    return gen(node.left) + '|' + gen(node.right);
  },
  Group: function Group(node) {
    var expression = gen(node.expression);

    if (node.capturing) {
      // A named group.
      if (node.name) {
        return '(?<' + (node.nameRaw || node.name) + '>' + expression + ')';
      }

      return '(' + expression + ')';
    }

    return '(?:' + expression + ')';
  },
  Backreference: function Backreference(node) {
    switch (node.kind) {
      case 'number':
        return '\\' + node.reference;
      case 'name':
        return '\\k<' + (node.referenceRaw || node.reference) + '>';
      default:
        throw new TypeError('Unknown Backreference kind: ' + node.kind);
    }
  },
  Assertion: function Assertion(node) {
    switch (node.kind) {
      case '^':
      case '$':
      case '\\b':
      case '\\B':
        return node.kind;

      case 'Lookahead':
        {
          var assertion = gen(node.assertion);

          if (node.negative) {
            return '(?!' + assertion + ')';
          }

          return '(?=' + assertion + ')';
        }

      case 'Lookbehind':
        {
          var _assertion = gen(node.assertion);

          if (node.negative) {
            return '(?<!' + _assertion + ')';
          }

          return '(?<=' + _assertion + ')';
        }

      default:
        throw new TypeError('Unknown Assertion kind: ' + node.kind);
    }
  },
  CharacterClass: function CharacterClass(node) {
    var expressions = node.expressions.map(gen).join('');

    if (node.negative) {
      return '[^' + expressions + ']';
    }

    return '[' + expressions + ']';
  },
  ClassRange: function ClassRange(node) {
    return gen(node.from) + '-' + gen(node.to);
  },
  Repetition: function Repetition(node) {
    return '' + gen(node.expression) + gen(node.quantifier);
  },
  Quantifier: function Quantifier(node) {
    var quantifier = void 0;
    var greedy = node.greedy ? '' : '?';

    switch (node.kind) {
      case '+':
      case '?':
      case '*':
        quantifier = node.kind;
        break;
      case 'Range':
        // Exact: {1}
        if (node.from === node.to) {
          quantifier = '{' + node.from + '}';
        }
        // Open: {1,}
        else if (!node.to) {
            quantifier = '{' + node.from + ',}';
          }
          // Closed: {1,3}
          else {
              quantifier = '{' + node.from + ',' + node.to + '}';
            }
        break;
      default:
        throw new TypeError('Unknown Quantifier kind: ' + node.kind);
    }

    return '' + quantifier + greedy;
  },
  Char: function Char(node) {
    var value = node.value;

    switch (node.kind) {
      case 'simple':
        {
          if (node.escaped) {
            return '\\' + value;
          }
          return value;
        }

      case 'hex':
      case 'unicode':
      case 'oct':
      case 'decimal':
      case 'control':
      case 'meta':
        return value;

      default:
        throw new TypeError('Unknown Char kind: ' + node.kind);
    }
  },
  UnicodeProperty: function UnicodeProperty(node) {
    var escapeChar = node.negative ? 'P' : 'p';
    var namePart = void 0;

    if (!node.shorthand && !node.binary) {
      namePart = node.name + '=';
    } else {
      namePart = '';
    }

    return '\\' + escapeChar + '{' + namePart + node.value + '}';
  }
};

module.exports = {
  /**
   * Generates a regexp string from an AST.
   *
   * @param Object ast - an AST node
   */
  generate: gen
};
},{}],18:[function(require,module,exports){
/**
 * The MIT License (MIT)
 * Copyright (c) 2017-present Dmitry Soshnikov <dmitry.soshnikov@gmail.com>
 */

'use strict';

// DFA minization.

/**
 * Map from state to current set it goes.
 */

var _slicedToArray = function () { function sliceIterator(arr, i) { var _arr = []; var _n = true; var _d = false; var _e = undefined; try { for (var _i = arr[Symbol.iterator](), _s; !(_n = (_s = _i.next()).done); _n = true) { _arr.push(_s.value); if (i && _arr.length === i) break; } } catch (err) { _d = true; _e = err; } finally { try { if (!_n && _i["return"]) _i["return"](); } finally { if (_d) throw _e; } } return _arr; } return function (arr, i) { if (Array.isArray(arr)) { return arr; } else if (Symbol.iterator in Object(arr)) { return sliceIterator(arr, i); } else { throw new TypeError("Invalid attempt to destructure non-iterable instance"); } }; }();

function _toArray(arr) { return Array.isArray(arr) ? arr : Array.from(arr); }

function _toConsumableArray(arr) { if (Array.isArray(arr)) { for (var i = 0, arr2 = Array(arr.length); i < arr.length; i++) { arr2[i] = arr[i]; } return arr2; } else { return Array.from(arr); } }

var currentTransitionMap = null;

/**
 * Takes a DFA, and returns a minimized version of it
 * compressing some states to groups (using standard, 0-, 1-,
 * 2-, ... N-equivalence algorithm).
 */
function minimize(dfa) {
  var table = dfa.getTransitionTable();
  var allStates = Object.keys(table);
  var alphabet = dfa.getAlphabet();
  var accepting = dfa.getAcceptingStateNumbers();

  currentTransitionMap = {};

  var nonAccepting = new Set();

  allStates.forEach(function (state) {
    state = Number(state);
    var isAccepting = accepting.has(state);

    if (isAccepting) {
      currentTransitionMap[state] = accepting;
    } else {
      nonAccepting.add(state);
      currentTransitionMap[state] = nonAccepting;
    }
  });

  // ---------------------------------------------------------------------------
  // Step 1: build equivalent sets.

  // All [1..N] equivalent sets.
  var all = [
  // 0-equivalent sets.
  [nonAccepting, accepting].filter(function (set) {
    return set.size > 0;
  })];

  var current = void 0;
  var previous = void 0;

  // Top of the stack is the current list of sets to analyze.
  current = all[all.length - 1];

  // Previous set (to check whether we need to stop).
  previous = all[all.length - 2];

  // Until we'll not have the same N and N-1 equivalent rows.

  var _loop = function _loop() {
    var newTransitionMap = {};

    var _iteratorNormalCompletion3 = true;
    var _didIteratorError3 = false;
    var _iteratorError3 = undefined;

    try {
      for (var _iterator3 = current[Symbol.iterator](), _step3; !(_iteratorNormalCompletion3 = (_step3 = _iterator3.next()).done); _iteratorNormalCompletion3 = true) {
        var _set = _step3.value;

        // Handled states for this set.
        var handledStates = {};

        var _set2 = _toArray(_set),
            first = _set2[0],
            rest = _set2.slice(1);

        handledStates[first] = new Set([first]);

        // Have to compare each from the rest states with
        // the already handled states, and see if they are equivalent.
        var _iteratorNormalCompletion4 = true;
        var _didIteratorError4 = false;
        var _iteratorError4 = undefined;

        try {
          restSets: for (var _iterator4 = rest[Symbol.iterator](), _step4; !(_iteratorNormalCompletion4 = (_step4 = _iterator4.next()).done); _iteratorNormalCompletion4 = true) {
            var state = _step4.value;
            var _iteratorNormalCompletion5 = true;
            var _didIteratorError5 = false;
            var _iteratorError5 = undefined;

            try {
              for (var _iterator5 = Object.keys(handledStates)[Symbol.iterator](), _step5; !(_iteratorNormalCompletion5 = (_step5 = _iterator5.next()).done); _iteratorNormalCompletion5 = true) {
                var handledState = _step5.value;

                // This and some previously handled state are equivalent --
                // just append this state to the same set.
                if (areEquivalent(state, handledState, table, alphabet)) {
                  handledStates[handledState].add(state);
                  handledStates[state] = handledStates[handledState];
                  continue restSets;
                }
              }
              // Else, this state is not equivalent to any of the
              // handled states -- allocate a new set for it.
            } catch (err) {
              _didIteratorError5 = true;
              _iteratorError5 = err;
            } finally {
              try {
                if (!_iteratorNormalCompletion5 && _iterator5.return) {
                  _iterator5.return();
                }
              } finally {
                if (_didIteratorError5) {
                  throw _iteratorError5;
                }
              }
            }

            handledStates[state] = new Set([state]);
          }
        } catch (err) {
          _didIteratorError4 = true;
          _iteratorError4 = err;
        } finally {
          try {
            if (!_iteratorNormalCompletion4 && _iterator4.return) {
              _iterator4.return();
            }
          } finally {
            if (_didIteratorError4) {
              throw _iteratorError4;
            }
          }
        }

        // Add these handled states to all states map.


        Object.assign(newTransitionMap, handledStates);
      }

      // Update current transition map for the handled row.
    } catch (err) {
      _didIteratorError3 = true;
      _iteratorError3 = err;
    } finally {
      try {
        if (!_iteratorNormalCompletion3 && _iterator3.return) {
          _iterator3.return();
        }
      } finally {
        if (_didIteratorError3) {
          throw _iteratorError3;
        }
      }
    }

    currentTransitionMap = newTransitionMap;

    var newSets = new Set(Object.keys(newTransitionMap).map(function (state) {
      return newTransitionMap[state];
    }));

    all.push([].concat(_toConsumableArray(newSets)));

    // Top of the stack is the current.
    current = all[all.length - 1];

    // Previous set.
    previous = all[all.length - 2];
  };

  while (!sameRow(current, previous)) {
    _loop();
  }

  // ---------------------------------------------------------------------------
  // Step 2: build minimized table from the equivalent sets.

  // Remap state numbers from sets to index-based.
  var remaped = new Map();
  var idx = 1;
  current.forEach(function (set) {
    return remaped.set(set, idx++);
  });

  // Build the minimized table from the calculated equivalent sets.
  var minimizedTable = {};

  var minimizedAcceptingStates = new Set();

  var updateAcceptingStates = function updateAcceptingStates(set, idx) {
    var _iteratorNormalCompletion = true;
    var _didIteratorError = false;
    var _iteratorError = undefined;

    try {
      for (var _iterator = set[Symbol.iterator](), _step; !(_iteratorNormalCompletion = (_step = _iterator.next()).done); _iteratorNormalCompletion = true) {
        var state = _step.value;

        if (accepting.has(state)) {
          minimizedAcceptingStates.add(idx);
        }
      }
    } catch (err) {
      _didIteratorError = true;
      _iteratorError = err;
    } finally {
      try {
        if (!_iteratorNormalCompletion && _iterator.return) {
          _iterator.return();
        }
      } finally {
        if (_didIteratorError) {
          throw _iteratorError;
        }
      }
    }
  };

  var _iteratorNormalCompletion2 = true;
  var _didIteratorError2 = false;
  var _iteratorError2 = undefined;

  try {
    for (var _iterator2 = remaped.entries()[Symbol.iterator](), _step2; !(_iteratorNormalCompletion2 = (_step2 = _iterator2.next()).done); _iteratorNormalCompletion2 = true) {
      var _ref = _step2.value;

      var _ref2 = _slicedToArray(_ref, 2);

      var set = _ref2[0];
      var _idx = _ref2[1];

      minimizedTable[_idx] = {};
      var _iteratorNormalCompletion6 = true;
      var _didIteratorError6 = false;
      var _iteratorError6 = undefined;

      try {
        for (var _iterator6 = alphabet[Symbol.iterator](), _step6; !(_iteratorNormalCompletion6 = (_step6 = _iterator6.next()).done); _iteratorNormalCompletion6 = true) {
          var symbol = _step6.value;

          updateAcceptingStates(set, _idx);

          // Determine original transition for this symbol from the set.
          var originalTransition = void 0;
          var _iteratorNormalCompletion7 = true;
          var _didIteratorError7 = false;
          var _iteratorError7 = undefined;

          try {
            for (var _iterator7 = set[Symbol.iterator](), _step7; !(_iteratorNormalCompletion7 = (_step7 = _iterator7.next()).done); _iteratorNormalCompletion7 = true) {
              var originalState = _step7.value;

              originalTransition = table[originalState][symbol];
              if (originalTransition) {
                break;
              }
            }
          } catch (err) {
            _didIteratorError7 = true;
            _iteratorError7 = err;
          } finally {
            try {
              if (!_iteratorNormalCompletion7 && _iterator7.return) {
                _iterator7.return();
              }
            } finally {
              if (_didIteratorError7) {
                throw _iteratorError7;
              }
            }
          }

          if (originalTransition) {
            minimizedTable[_idx][symbol] = remaped.get(currentTransitionMap[originalTransition]);
          }
        }
      } catch (err) {
        _didIteratorError6 = true;
        _iteratorError6 = err;
      } finally {
        try {
          if (!_iteratorNormalCompletion6 && _iterator6.return) {
            _iterator6.return();
          }
        } finally {
          if (_didIteratorError6) {
            throw _iteratorError6;
          }
        }
      }
    }

    // Update the table, and accepting states on the original DFA.
  } catch (err) {
    _didIteratorError2 = true;
    _iteratorError2 = err;
  } finally {
    try {
      if (!_iteratorNormalCompletion2 && _iterator2.return) {
        _iterator2.return();
      }
    } finally {
      if (_didIteratorError2) {
        throw _iteratorError2;
      }
    }
  }

  dfa.setTransitionTable(minimizedTable);
  dfa.setAcceptingStateNumbers(minimizedAcceptingStates);

  return dfa;
}

function sameRow(r1, r2) {
  if (!r2) {
    return false;
  }

  if (r1.length !== r2.length) {
    return false;
  }

  for (var i = 0; i < r1.length; i++) {
    var s1 = r1[i];
    var s2 = r2[i];

    if (s1.size !== s2.size) {
      return false;
    }

    if ([].concat(_toConsumableArray(s1)).sort().join(',') !== [].concat(_toConsumableArray(s2)).sort().join(',')) {
      return false;
    }
  }

  return true;
}

/**
 * Checks whether two states are N-equivalent, i.e. whether they go
 * to the same set on a symbol.
 */
function areEquivalent(s1, s2, table, alphabet) {
  var _iteratorNormalCompletion8 = true;
  var _didIteratorError8 = false;
  var _iteratorError8 = undefined;

  try {
    for (var _iterator8 = alphabet[Symbol.iterator](), _step8; !(_iteratorNormalCompletion8 = (_step8 = _iterator8.next()).done); _iteratorNormalCompletion8 = true) {
      var symbol = _step8.value;

      if (!goToSameSet(s1, s2, table, symbol)) {
        return false;
      }
    }
  } catch (err) {
    _didIteratorError8 = true;
    _iteratorError8 = err;
  } finally {
    try {
      if (!_iteratorNormalCompletion8 && _iterator8.return) {
        _iterator8.return();
      }
    } finally {
      if (_didIteratorError8) {
        throw _iteratorError8;
      }
    }
  }

  return true;
}

/**
 * Checks whether states go to the same set.
 */
function goToSameSet(s1, s2, table, symbol) {
  if (!currentTransitionMap[s1] || !currentTransitionMap[s2]) {
    return false;
  }

  var originalTransitionS1 = table[s1][symbol];
  var originalTransitionS2 = table[s2][symbol];

  // If no actual transition on this symbol, treat it as positive.
  if (!originalTransitionS1 && !originalTransitionS2) {
    return true;
  }

  // Otherwise, check if they are in the same sets.
  return currentTransitionMap[s1].has(originalTransitionS1) && currentTransitionMap[s2].has(originalTransitionS2);
}

module.exports = {
  minimize: minimize
};
},{}],19:[function(require,module,exports){
/**
 * The MIT License (MIT)
 * Copyright (c) 2017-present Dmitry Soshnikov <dmitry.soshnikov@gmail.com>
 */

'use strict';

var _createClass = function () { function defineProperties(target, props) { for (var i = 0; i < props.length; i++) { var descriptor = props[i]; descriptor.enumerable = descriptor.enumerable || false; descriptor.configurable = true; if ("value" in descriptor) descriptor.writable = true; Object.defineProperty(target, descriptor.key, descriptor); } } return function (Constructor, protoProps, staticProps) { if (protoProps) defineProperties(Constructor.prototype, protoProps); if (staticProps) defineProperties(Constructor, staticProps); return Constructor; }; }();

function _toConsumableArray(arr) { if (Array.isArray(arr)) { for (var i = 0, arr2 = Array(arr.length); i < arr.length; i++) { arr2[i] = arr[i]; } return arr2; } else { return Array.from(arr); } }

function _classCallCheck(instance, Constructor) { if (!(instance instanceof Constructor)) { throw new TypeError("Cannot call a class as a function"); } }

var DFAMinimizer = require('./dfa-minimizer');

var _require = require('../special-symbols'),
    EPSILON_CLOSURE = _require.EPSILON_CLOSURE;

/**
 * DFA is build by converting from NFA (subset construction).
 */


var DFA = function () {
  function DFA(nfa) {
    _classCallCheck(this, DFA);

    this._nfa = nfa;
  }

  /**
   * Minimizes DFA.
   */


  _createClass(DFA, [{
    key: 'minimize',
    value: function minimize() {
      this.getTransitionTable();

      this._originalAcceptingStateNumbers = this._acceptingStateNumbers;
      this._originalTransitionTable = this._transitionTable;

      DFAMinimizer.minimize(this);
    }

    /**
     * Returns alphabet for this DFA.
     */

  }, {
    key: 'getAlphabet',
    value: function getAlphabet() {
      return this._nfa.getAlphabet();
    }

    /**
     * Returns accepting states.
     */

  }, {
    key: 'getAcceptingStateNumbers',
    value: function getAcceptingStateNumbers() {
      if (!this._acceptingStateNumbers) {
        // Accepting states are determined during table construction.
        this.getTransitionTable();
      }

      return this._acceptingStateNumbers;
    }

    /**
     * Returns original accepting states.
     */

  }, {
    key: 'getOriginaAcceptingStateNumbers',
    value: function getOriginaAcceptingStateNumbers() {
      if (!this._originalAcceptingStateNumbers) {
        // Accepting states are determined during table construction.
        this.getTransitionTable();
      }

      return this._originalAcceptingStateNumbers;
    }

    /**
     * Sets transition table.
     */

  }, {
    key: 'setTransitionTable',
    value: function setTransitionTable(table) {
      this._transitionTable = table;
    }

    /**
     * Sets accepting states.
     */

  }, {
    key: 'setAcceptingStateNumbers',
    value: function setAcceptingStateNumbers(stateNumbers) {
      this._acceptingStateNumbers = stateNumbers;
    }

    /**
     * DFA transition table is built from NFA table.
     */

  }, {
    key: 'getTransitionTable',
    value: function getTransitionTable() {
      var _this = this;

      if (this._transitionTable) {
        return this._transitionTable;
      }

      // Calculate from NFA transition table.
      var nfaTable = this._nfa.getTransitionTable();
      var nfaStates = Object.keys(nfaTable);

      this._acceptingStateNumbers = new Set();

      // Start state of DFA is E(S[nfa])
      var startState = nfaTable[nfaStates[0]][EPSILON_CLOSURE];

      // Init the worklist (states which should be in the DFA).
      var worklist = [startState];

      var alphabet = this.getAlphabet();
      var nfaAcceptingStates = this._nfa.getAcceptingStateNumbers();

      var dfaTable = {};

      // Determine whether the combined DFA state is accepting.
      var updateAcceptingStates = function updateAcceptingStates(states) {
        var _iteratorNormalCompletion = true;
        var _didIteratorError = false;
        var _iteratorError = undefined;

        try {
          for (var _iterator = nfaAcceptingStates[Symbol.iterator](), _step; !(_iteratorNormalCompletion = (_step = _iterator.next()).done); _iteratorNormalCompletion = true) {
            var nfaAcceptingState = _step.value;

            // If any of the states from NFA is accepting, DFA's
            // state is accepting as well.
            if (states.indexOf(nfaAcceptingState) !== -1) {
              _this._acceptingStateNumbers.add(states.join(','));
              break;
            }
          }
        } catch (err) {
          _didIteratorError = true;
          _iteratorError = err;
        } finally {
          try {
            if (!_iteratorNormalCompletion && _iterator.return) {
              _iterator.return();
            }
          } finally {
            if (_didIteratorError) {
              throw _iteratorError;
            }
          }
        }
      };

      while (worklist.length > 0) {
        var states = worklist.shift();
        var dfaStateLabel = states.join(',');
        dfaTable[dfaStateLabel] = {};

        var _iteratorNormalCompletion2 = true;
        var _didIteratorError2 = false;
        var _iteratorError2 = undefined;

        try {
          for (var _iterator2 = alphabet[Symbol.iterator](), _step2; !(_iteratorNormalCompletion2 = (_step2 = _iterator2.next()).done); _iteratorNormalCompletion2 = true) {
            var symbol = _step2.value;

            var onSymbol = [];

            // Determine whether the combined state is accepting.
            updateAcceptingStates(states);

            var _iteratorNormalCompletion3 = true;
            var _didIteratorError3 = false;
            var _iteratorError3 = undefined;

            try {
              for (var _iterator3 = states[Symbol.iterator](), _step3; !(_iteratorNormalCompletion3 = (_step3 = _iterator3.next()).done); _iteratorNormalCompletion3 = true) {
                var state = _step3.value;

                var nfaStatesOnSymbol = nfaTable[state][symbol];
                if (!nfaStatesOnSymbol) {
                  continue;
                }

                var _iteratorNormalCompletion4 = true;
                var _didIteratorError4 = false;
                var _iteratorError4 = undefined;

                try {
                  for (var _iterator4 = nfaStatesOnSymbol[Symbol.iterator](), _step4; !(_iteratorNormalCompletion4 = (_step4 = _iterator4.next()).done); _iteratorNormalCompletion4 = true) {
                    var nfaStateOnSymbol = _step4.value;

                    if (!nfaTable[nfaStateOnSymbol]) {
                      continue;
                    }
                    onSymbol.push.apply(onSymbol, _toConsumableArray(nfaTable[nfaStateOnSymbol][EPSILON_CLOSURE]));
                  }
                } catch (err) {
                  _didIteratorError4 = true;
                  _iteratorError4 = err;
                } finally {
                  try {
                    if (!_iteratorNormalCompletion4 && _iterator4.return) {
                      _iterator4.return();
                    }
                  } finally {
                    if (_didIteratorError4) {
                      throw _iteratorError4;
                    }
                  }
                }
              }
            } catch (err) {
              _didIteratorError3 = true;
              _iteratorError3 = err;
            } finally {
              try {
                if (!_iteratorNormalCompletion3 && _iterator3.return) {
                  _iterator3.return();
                }
              } finally {
                if (_didIteratorError3) {
                  throw _iteratorError3;
                }
              }
            }

            var dfaStatesOnSymbolSet = new Set(onSymbol);
            var dfaStatesOnSymbol = [].concat(_toConsumableArray(dfaStatesOnSymbolSet));

            if (dfaStatesOnSymbol.length > 0) {
              var dfaOnSymbolStr = dfaStatesOnSymbol.join(',');

              dfaTable[dfaStateLabel][symbol] = dfaOnSymbolStr;

              if (!dfaTable.hasOwnProperty(dfaOnSymbolStr)) {
                worklist.unshift(dfaStatesOnSymbol);
              }
            }
          }
        } catch (err) {
          _didIteratorError2 = true;
          _iteratorError2 = err;
        } finally {
          try {
            if (!_iteratorNormalCompletion2 && _iterator2.return) {
              _iterator2.return();
            }
          } finally {
            if (_didIteratorError2) {
              throw _iteratorError2;
            }
          }
        }
      }

      return this._transitionTable = this._remapStateNumbers(dfaTable);
    }

    /**
     * Remaps state numbers in the resulting table:
     * combined states '1,2,3' -> 1, '3,4' -> 2, etc.
     */

  }, {
    key: '_remapStateNumbers',
    value: function _remapStateNumbers(calculatedDFATable) {
      var newStatesMap = {};

      this._originalTransitionTable = calculatedDFATable;
      var transitionTable = {};

      Object.keys(calculatedDFATable).forEach(function (originalNumber, newNumber) {
        newStatesMap[originalNumber] = newNumber + 1;
      });

      for (var originalNumber in calculatedDFATable) {
        var originalRow = calculatedDFATable[originalNumber];
        var row = {};

        for (var symbol in originalRow) {
          row[symbol] = newStatesMap[originalRow[symbol]];
        }

        transitionTable[newStatesMap[originalNumber]] = row;
      }

      // Remap accepting states.
      this._originalAcceptingStateNumbers = this._acceptingStateNumbers;
      this._acceptingStateNumbers = new Set();

      var _iteratorNormalCompletion5 = true;
      var _didIteratorError5 = false;
      var _iteratorError5 = undefined;

      try {
        for (var _iterator5 = this._originalAcceptingStateNumbers[Symbol.iterator](), _step5; !(_iteratorNormalCompletion5 = (_step5 = _iterator5.next()).done); _iteratorNormalCompletion5 = true) {
          var _originalNumber = _step5.value;

          this._acceptingStateNumbers.add(newStatesMap[_originalNumber]);
        }
      } catch (err) {
        _didIteratorError5 = true;
        _iteratorError5 = err;
      } finally {
        try {
          if (!_iteratorNormalCompletion5 && _iterator5.return) {
            _iterator5.return();
          }
        } finally {
          if (_didIteratorError5) {
            throw _iteratorError5;
          }
        }
      }

      return transitionTable;
    }

    /**
     * Returns original DFA table, where state numbers
     * are combined numbers from NFA.
     */

  }, {
    key: 'getOriginalTransitionTable',
    value: function getOriginalTransitionTable() {
      if (!this._originalTransitionTable) {
        // Original table is determined during table construction.
        this.getTransitionTable();
      }
      return this._originalTransitionTable;
    }

    /**
     * Checks whether this DFA accepts a string.
     */

  }, {
    key: 'matches',
    value: function matches(string) {
      var state = 1;
      var i = 0;
      var table = this.getTransitionTable();

      while (string[i]) {
        state = table[state][string[i++]];
        if (!state) {
          return false;
        }
      }

      if (!this.getAcceptingStateNumbers().has(state)) {
        return false;
      }

      return true;
    }
  }]);

  return DFA;
}();

module.exports = DFA;
},{"../special-symbols":25,"./dfa-minimizer":18}],20:[function(require,module,exports){
/**
 * The MIT License (MIT)
 * Copyright (c) 2017-present Dmitry Soshnikov <dmitry.soshnikov@gmail.com>
 */

'use strict';

var NFA = require('./nfa/nfa');
var DFA = require('./dfa/dfa');

var nfaFromRegExp = require('./nfa/nfa-from-regexp');
var builders = require('./nfa/builders');

module.exports = {

  /**
   * Export NFA and DFA classes.
   */
  NFA: NFA,
  DFA: DFA,

  /**
   * Expose builders.
   */
  builders: builders,

  /**
   * Builds an NFA for the passed regexp.
   *
   * @param string | AST | RegExp:
   *
   *   a regular expression in different representations: a string,
   *   a RegExp object, or an AST.
   */
  toNFA: function toNFA(regexp) {
    return nfaFromRegExp.build(regexp);
  },


  /**
   * Builds DFA for the passed regexp.
   *
   * @param string | AST | RegExp:
   *
   *   a regular expression in different representations: a string,
   *   a RegExp object, or an AST.
   */
  toDFA: function toDFA(regexp) {
    return new DFA(this.toNFA(regexp));
  },


  /**
   * Returns true if regexp accepts the string.
   */
  test: function test(regexp, string) {
    return this.toDFA(regexp).matches(string);
  }
};
},{"./dfa/dfa":19,"./nfa/builders":21,"./nfa/nfa":24,"./nfa/nfa-from-regexp":22}],21:[function(require,module,exports){
/**
 * The MIT License (MIT)
 * Copyright (c) 2017-present Dmitry Soshnikov <dmitry.soshnikov@gmail.com>
 */

'use strict';

var NFA = require('./nfa');
var NFAState = require('./nfa-state');

var _require = require('../special-symbols'),
    EPSILON = _require.EPSILON;

// -----------------------------------------------------------------------------
// Char NFA fragment: `c`

/**
 * Char factory.
 *
 * Creates an NFA fragment for a single char.
 *
 * [in] --c--> [out]
 */


function char(c) {
  var inState = new NFAState();
  var outState = new NFAState({
    accepting: true
  });

  return new NFA(inState.addTransition(c, outState), outState);
}

// -----------------------------------------------------------------------------
// Epsilon NFA fragment

/**
 * Epsilon factory.
 *
 * Creates an NFA fragment for ε (recognizes an empty string).
 *
 * [in] --ε--> [out]
 */
function e() {
  return char(EPSILON);
}

// -----------------------------------------------------------------------------
// Alteration NFA fragment: `abc`

/**
 * Creates a connection between two NFA fragments on epsilon transition.
 *
 * [in-a] --a--> [out-a] --ε--> [in-b] --b--> [out-b]
 */
function altPair(first, second) {
  first.out.accepting = false;
  second.out.accepting = true;

  first.out.addTransition(EPSILON, second.in);

  return new NFA(first.in, second.out);
}

/**
 * Alteration factory.
 *
 * Creates a alteration NFA for (at least) two NFA-fragments.
 */
function alt(first) {
  for (var _len = arguments.length, fragments = Array(_len > 1 ? _len - 1 : 0), _key = 1; _key < _len; _key++) {
    fragments[_key - 1] = arguments[_key];
  }

  var _iteratorNormalCompletion = true;
  var _didIteratorError = false;
  var _iteratorError = undefined;

  try {
    for (var _iterator = fragments[Symbol.iterator](), _step; !(_iteratorNormalCompletion = (_step = _iterator.next()).done); _iteratorNormalCompletion = true) {
      var fragment = _step.value;

      first = altPair(first, fragment);
    }
  } catch (err) {
    _didIteratorError = true;
    _iteratorError = err;
  } finally {
    try {
      if (!_iteratorNormalCompletion && _iterator.return) {
        _iterator.return();
      }
    } finally {
      if (_didIteratorError) {
        throw _iteratorError;
      }
    }
  }

  return first;
}

// -----------------------------------------------------------------------------
// Disjunction NFA fragment: `a|b`

/**
 * Creates a disjunction choice between two fragments.
 */
function orPair(first, second) {
  var inState = new NFAState();
  var outState = new NFAState();

  inState.addTransition(EPSILON, first.in);
  inState.addTransition(EPSILON, second.in);

  outState.accepting = true;
  first.out.accepting = false;
  second.out.accepting = false;

  first.out.addTransition(EPSILON, outState);
  second.out.addTransition(EPSILON, outState);

  return new NFA(inState, outState);
}

/**
 * Disjunction factory.
 *
 * Creates a disjunction NFA for (at least) two NFA-fragments.
 */
function or(first) {
  for (var _len2 = arguments.length, fragments = Array(_len2 > 1 ? _len2 - 1 : 0), _key2 = 1; _key2 < _len2; _key2++) {
    fragments[_key2 - 1] = arguments[_key2];
  }

  var _iteratorNormalCompletion2 = true;
  var _didIteratorError2 = false;
  var _iteratorError2 = undefined;

  try {
    for (var _iterator2 = fragments[Symbol.iterator](), _step2; !(_iteratorNormalCompletion2 = (_step2 = _iterator2.next()).done); _iteratorNormalCompletion2 = true) {
      var fragment = _step2.value;

      first = orPair(first, fragment);
    }
  } catch (err) {
    _didIteratorError2 = true;
    _iteratorError2 = err;
  } finally {
    try {
      if (!_iteratorNormalCompletion2 && _iterator2.return) {
        _iterator2.return();
      }
    } finally {
      if (_didIteratorError2) {
        throw _iteratorError2;
      }
    }
  }

  return first;
}

// -----------------------------------------------------------------------------
// Kleene-closure

/**
 * Kleene star/closure.
 *
 * a*
 */
function repExplicit(fragment) {
  var inState = new NFAState();
  var outState = new NFAState({
    accepting: true
  });

  // 0 or more.
  inState.addTransition(EPSILON, fragment.in);
  inState.addTransition(EPSILON, outState);

  fragment.out.accepting = false;
  fragment.out.addTransition(EPSILON, outState);
  outState.addTransition(EPSILON, fragment.in);

  return new NFA(inState, outState);
}

/**
 * Optimized Kleene-star: just adds ε-transitions from
 * input to the output, and back.
 */
function rep(fragment) {
  fragment.in.addTransition(EPSILON, fragment.out);
  fragment.out.addTransition(EPSILON, fragment.in);
  return fragment;
}

/**
 * Optimized Plus: just adds ε-transitions from
 * the output to the input.
 */
function plusRep(fragment) {
  fragment.out.addTransition(EPSILON, fragment.in);
  return fragment;
}

/**
 * Optimized ? repetition: just adds ε-transitions from
 * the input to the output.
 */
function questionRep(fragment) {
  fragment.in.addTransition(EPSILON, fragment.out);
  return fragment;
}

module.exports = {
  alt: alt,
  char: char,
  e: e,
  or: or,
  rep: rep,
  repExplicit: repExplicit,
  plusRep: plusRep,
  questionRep: questionRep
};
},{"../special-symbols":25,"./nfa":24,"./nfa-state":23}],22:[function(require,module,exports){
/**
 * The MIT License (MIT)
 * Copyright (c) 2017-present Dmitry Soshnikov <dmitry.soshnikov@gmail.com>
 */

'use strict';

function _toConsumableArray(arr) { if (Array.isArray(arr)) { for (var i = 0, arr2 = Array(arr.length); i < arr.length; i++) { arr2[i] = arr[i]; } return arr2; } else { return Array.from(arr); } }

var parser = require('../../../parser');

var _require = require('./builders'),
    alt = _require.alt,
    char = _require.char,
    or = _require.or,
    rep = _require.rep,
    plusRep = _require.plusRep,
    questionRep = _require.questionRep;

/**
 * Helper `gen` function calls node type handler.
 */


function gen(node) {
  if (node && !generator[node.type]) {
    throw new Error(node.type + ' is not supported in NFA/DFA interpreter.');
  }

  return node ? generator[node.type](node) : '';
}

/**
 * AST handler.
 */
var generator = {
  RegExp: function RegExp(node) {
    if (node.flags !== '') {
      throw new Error('NFA/DFA: Flags are not supported yet.');
    }

    return gen(node.body);
  },
  Alternative: function Alternative(node) {
    var fragments = (node.expressions || []).map(gen);
    return alt.apply(undefined, _toConsumableArray(fragments));
  },
  Disjunction: function Disjunction(node) {
    return or(gen(node.left), gen(node.right));
  },
  Repetition: function Repetition(node) {
    switch (node.quantifier.kind) {
      case '*':
        return rep(gen(node.expression));
      case '+':
        return plusRep(gen(node.expression));
      case '?':
        return questionRep(gen(node.expression));
      default:
        throw new Error('Unknown repeatition: ' + node.quantifier.kind + '.');
    }
  },
  Char: function Char(node) {
    if (node.kind !== 'simple') {
      throw new Error('NFA/DFA: Only simple chars are supported yet.');
    }

    return char(node.value);
  },
  Group: function Group(node) {
    return gen(node.expression);
  }
};

module.exports = {
  /**
   * Builds an NFA from the passed regexp.
   */
  build: function build(regexp) {
    var ast = regexp;

    if (regexp instanceof RegExp) {
      regexp = '' + regexp;
    }

    if (typeof regexp === 'string') {
      ast = parser.parse(regexp, {
        captureLocations: true
      });
    }

    return gen(ast);
  }
};
},{"../../../parser":46,"./builders":21}],23:[function(require,module,exports){
/**
 * The MIT License (MIT)
 * Copyright (c) 2017-present Dmitry Soshnikov <dmitry.soshnikov@gmail.com>
 */

'use strict';

var _createClass = function () { function defineProperties(target, props) { for (var i = 0; i < props.length; i++) { var descriptor = props[i]; descriptor.enumerable = descriptor.enumerable || false; descriptor.configurable = true; if ("value" in descriptor) descriptor.writable = true; Object.defineProperty(target, descriptor.key, descriptor); } } return function (Constructor, protoProps, staticProps) { if (protoProps) defineProperties(Constructor.prototype, protoProps); if (staticProps) defineProperties(Constructor, staticProps); return Constructor; }; }();

function _classCallCheck(instance, Constructor) { if (!(instance instanceof Constructor)) { throw new TypeError("Cannot call a class as a function"); } }

function _possibleConstructorReturn(self, call) { if (!self) { throw new ReferenceError("this hasn't been initialised - super() hasn't been called"); } return call && (typeof call === "object" || typeof call === "function") ? call : self; }

function _inherits(subClass, superClass) { if (typeof superClass !== "function" && superClass !== null) { throw new TypeError("Super expression must either be null or a function, not " + typeof superClass); } subClass.prototype = Object.create(superClass && superClass.prototype, { constructor: { value: subClass, enumerable: false, writable: true, configurable: true } }); if (superClass) Object.setPrototypeOf ? Object.setPrototypeOf(subClass, superClass) : subClass.__proto__ = superClass; }

var State = require('../state');

var _require = require('../special-symbols'),
    EPSILON = _require.EPSILON;

/**
 * NFA state.
 *
 * Allows nondeterministic transitions to several states on the
 * same symbol, and also epsilon-transitions.
 */


var NFAState = function (_State) {
  _inherits(NFAState, _State);

  function NFAState() {
    _classCallCheck(this, NFAState);

    return _possibleConstructorReturn(this, (NFAState.__proto__ || Object.getPrototypeOf(NFAState)).apply(this, arguments));
  }

  _createClass(NFAState, [{
    key: 'matches',


    /**
     * Whether this state matches a string.
     *
     * We maintain set of visited epsilon-states to avoid infinite loops
     * when an epsilon-transition goes eventually to itself.
     *
     * NOTE: this function is rather "educational", since we use DFA for strings
     * matching. DFA is built on top of NFA, and uses fast transition table.
     */
    value: function matches(string) {
      var visited = arguments.length > 1 && arguments[1] !== undefined ? arguments[1] : new Set();

      // An epsilon-state has been visited, stop to avoid infinite loop.
      if (visited.has(this)) {
        return false;
      }

      visited.add(this);

      // No symbols left..
      if (string.length === 0) {
        // .. and we're in the accepting state.
        if (this.accepting) {
          return true;
        }

        // Check if we can reach any accepting state from
        // on the epsilon transitions.
        var _iteratorNormalCompletion = true;
        var _didIteratorError = false;
        var _iteratorError = undefined;

        try {
          for (var _iterator = this.getTransitionsOnSymbol(EPSILON)[Symbol.iterator](), _step; !(_iteratorNormalCompletion = (_step = _iterator.next()).done); _iteratorNormalCompletion = true) {
            var nextState = _step.value;

            if (nextState.matches('', visited)) {
              return true;
            }
          }
        } catch (err) {
          _didIteratorError = true;
          _iteratorError = err;
        } finally {
          try {
            if (!_iteratorNormalCompletion && _iterator.return) {
              _iterator.return();
            }
          } finally {
            if (_didIteratorError) {
              throw _iteratorError;
            }
          }
        }

        return false;
      }

      // Else, we get some symbols.
      var symbol = string[0];
      var rest = string.slice(1);

      var symbolTransitions = this.getTransitionsOnSymbol(symbol);
      var _iteratorNormalCompletion2 = true;
      var _didIteratorError2 = false;
      var _iteratorError2 = undefined;

      try {
        for (var _iterator2 = symbolTransitions[Symbol.iterator](), _step2; !(_iteratorNormalCompletion2 = (_step2 = _iterator2.next()).done); _iteratorNormalCompletion2 = true) {
          var _nextState = _step2.value;

          if (_nextState.matches(rest)) {
            return true;
          }
        }

        // If we couldn't match on symbol, check still epsilon-transitions
        // without consuming the symbol (i.e. continue from `string`, not `rest`).
      } catch (err) {
        _didIteratorError2 = true;
        _iteratorError2 = err;
      } finally {
        try {
          if (!_iteratorNormalCompletion2 && _iterator2.return) {
            _iterator2.return();
          }
        } finally {
          if (_didIteratorError2) {
            throw _iteratorError2;
          }
        }
      }

      var _iteratorNormalCompletion3 = true;
      var _didIteratorError3 = false;
      var _iteratorError3 = undefined;

      try {
        for (var _iterator3 = this.getTransitionsOnSymbol(EPSILON)[Symbol.iterator](), _step3; !(_iteratorNormalCompletion3 = (_step3 = _iterator3.next()).done); _iteratorNormalCompletion3 = true) {
          var _nextState2 = _step3.value;

          if (_nextState2.matches(string, visited)) {
            return true;
          }
        }
      } catch (err) {
        _didIteratorError3 = true;
        _iteratorError3 = err;
      } finally {
        try {
          if (!_iteratorNormalCompletion3 && _iterator3.return) {
            _iterator3.return();
          }
        } finally {
          if (_didIteratorError3) {
            throw _iteratorError3;
          }
        }
      }

      return false;
    }

    /**
     * Returns an ε-closure for this state:
     * self + all states following ε-transitions.
     */

  }, {
    key: 'getEpsilonClosure',
    value: function getEpsilonClosure() {
      var _this2 = this;

      if (!this._epsilonClosure) {
        (function () {
          var epsilonTransitions = _this2.getTransitionsOnSymbol(EPSILON);
          var closure = _this2._epsilonClosure = new Set();
          closure.add(_this2);
          var _iteratorNormalCompletion4 = true;
          var _didIteratorError4 = false;
          var _iteratorError4 = undefined;

          try {
            for (var _iterator4 = epsilonTransitions[Symbol.iterator](), _step4; !(_iteratorNormalCompletion4 = (_step4 = _iterator4.next()).done); _iteratorNormalCompletion4 = true) {
              var nextState = _step4.value;

              if (!closure.has(nextState)) {
                closure.add(nextState);
                var nextClosure = nextState.getEpsilonClosure();
                nextClosure.forEach(function (state) {
                  return closure.add(state);
                });
              }
            }
          } catch (err) {
            _didIteratorError4 = true;
            _iteratorError4 = err;
          } finally {
            try {
              if (!_iteratorNormalCompletion4 && _iterator4.return) {
                _iterator4.return();
              }
            } finally {
              if (_didIteratorError4) {
                throw _iteratorError4;
              }
            }
          }
        })();
      }

      return this._epsilonClosure;
    }
  }]);

  return NFAState;
}(State);

module.exports = NFAState;
},{"../special-symbols":25,"../state":26}],24:[function(require,module,exports){
/**
 * The MIT License (MIT)
 * Copyright (c) 2017-present Dmitry Soshnikov <dmitry.soshnikov@gmail.com>
 */

'use strict';

var _slicedToArray = function () { function sliceIterator(arr, i) { var _arr = []; var _n = true; var _d = false; var _e = undefined; try { for (var _i = arr[Symbol.iterator](), _s; !(_n = (_s = _i.next()).done); _n = true) { _arr.push(_s.value); if (i && _arr.length === i) break; } } catch (err) { _d = true; _e = err; } finally { try { if (!_n && _i["return"]) _i["return"](); } finally { if (_d) throw _e; } } return _arr; } return function (arr, i) { if (Array.isArray(arr)) { return arr; } else if (Symbol.iterator in Object(arr)) { return sliceIterator(arr, i); } else { throw new TypeError("Invalid attempt to destructure non-iterable instance"); } }; }();

var _createClass = function () { function defineProperties(target, props) { for (var i = 0; i < props.length; i++) { var descriptor = props[i]; descriptor.enumerable = descriptor.enumerable || false; descriptor.configurable = true; if ("value" in descriptor) descriptor.writable = true; Object.defineProperty(target, descriptor.key, descriptor); } } return function (Constructor, protoProps, staticProps) { if (protoProps) defineProperties(Constructor.prototype, protoProps); if (staticProps) defineProperties(Constructor, staticProps); return Constructor; }; }();

function _toConsumableArray(arr) { if (Array.isArray(arr)) { for (var i = 0, arr2 = Array(arr.length); i < arr.length; i++) { arr2[i] = arr[i]; } return arr2; } else { return Array.from(arr); } }

function _classCallCheck(instance, Constructor) { if (!(instance instanceof Constructor)) { throw new TypeError("Cannot call a class as a function"); } }

var _require = require('../special-symbols'),
    EPSILON = _require.EPSILON,
    EPSILON_CLOSURE = _require.EPSILON_CLOSURE;

/**
 * NFA fragment.
 *
 * NFA sub-fragments can be combined to a larger NFAs building
 * the resulting machine. Combining the fragments is done by patching
 * edges of the in- and out-states.
 *
 * 2-states implementation, `in`, and `out`. Eventually all transitions
 * go to the same `out`, which can further be connected via ε-transition
 * with other fragment.
 */


var NFA = function () {
  function NFA(inState, outState) {
    _classCallCheck(this, NFA);

    this.in = inState;
    this.out = outState;
  }

  /**
   * Tries to recognize a string based on this NFA fragment.
   */


  _createClass(NFA, [{
    key: 'matches',
    value: function matches(string) {
      return this.in.matches(string);
    }

    /**
     * Returns an alphabet for this NFA.
     */

  }, {
    key: 'getAlphabet',
    value: function getAlphabet() {
      if (!this._alphabet) {
        this._alphabet = new Set();
        var table = this.getTransitionTable();
        for (var state in table) {
          var transitions = table[state];
          for (var symbol in transitions) {
            if (symbol !== EPSILON_CLOSURE) {
              this._alphabet.add(symbol);
            }
          }
        }
      }
      return this._alphabet;
    }

    /**
     * Returns set of accepting states.
     */

  }, {
    key: 'getAcceptingStates',
    value: function getAcceptingStates() {
      if (!this._acceptingStates) {
        // States are determined during table construction.
        this.getTransitionTable();
      }
      return this._acceptingStates;
    }

    /**
     * Returns accepting state numbers.
     */

  }, {
    key: 'getAcceptingStateNumbers',
    value: function getAcceptingStateNumbers() {
      if (!this._acceptingStateNumbers) {
        this._acceptingStateNumbers = new Set();
        var _iteratorNormalCompletion = true;
        var _didIteratorError = false;
        var _iteratorError = undefined;

        try {
          for (var _iterator = this.getAcceptingStates()[Symbol.iterator](), _step; !(_iteratorNormalCompletion = (_step = _iterator.next()).done); _iteratorNormalCompletion = true) {
            var acceptingState = _step.value;

            this._acceptingStateNumbers.add(acceptingState.number);
          }
        } catch (err) {
          _didIteratorError = true;
          _iteratorError = err;
        } finally {
          try {
            if (!_iteratorNormalCompletion && _iterator.return) {
              _iterator.return();
            }
          } finally {
            if (_didIteratorError) {
              throw _iteratorError;
            }
          }
        }
      }
      return this._acceptingStateNumbers;
    }

    /**
     * Builds and returns transition table.
     */

  }, {
    key: 'getTransitionTable',
    value: function getTransitionTable() {
      var _this = this;

      if (!this._transitionTable) {
        this._transitionTable = {};
        this._acceptingStates = new Set();

        var visited = new Set();
        var symbols = new Set();

        var visitState = function visitState(state) {
          if (visited.has(state)) {
            return;
          }

          visited.add(state);
          state.number = visited.size;
          _this._transitionTable[state.number] = {};

          if (state.accepting) {
            _this._acceptingStates.add(state);
          }

          var transitions = state.getTransitions();

          var _iteratorNormalCompletion2 = true;
          var _didIteratorError2 = false;
          var _iteratorError2 = undefined;

          try {
            for (var _iterator2 = transitions[Symbol.iterator](), _step2; !(_iteratorNormalCompletion2 = (_step2 = _iterator2.next()).done); _iteratorNormalCompletion2 = true) {
              var _ref = _step2.value;

              var _ref2 = _slicedToArray(_ref, 2);

              var symbol = _ref2[0];
              var symbolTransitions = _ref2[1];

              var combinedState = [];
              symbols.add(symbol);
              var _iteratorNormalCompletion3 = true;
              var _didIteratorError3 = false;
              var _iteratorError3 = undefined;

              try {
                for (var _iterator3 = symbolTransitions[Symbol.iterator](), _step3; !(_iteratorNormalCompletion3 = (_step3 = _iterator3.next()).done); _iteratorNormalCompletion3 = true) {
                  var nextState = _step3.value;

                  visitState(nextState);
                  combinedState.push(nextState.number);
                }
              } catch (err) {
                _didIteratorError3 = true;
                _iteratorError3 = err;
              } finally {
                try {
                  if (!_iteratorNormalCompletion3 && _iterator3.return) {
                    _iterator3.return();
                  }
                } finally {
                  if (_didIteratorError3) {
                    throw _iteratorError3;
                  }
                }
              }

              _this._transitionTable[state.number][symbol] = combinedState;
            }
          } catch (err) {
            _didIteratorError2 = true;
            _iteratorError2 = err;
          } finally {
            try {
              if (!_iteratorNormalCompletion2 && _iterator2.return) {
                _iterator2.return();
              }
            } finally {
              if (_didIteratorError2) {
                throw _iteratorError2;
              }
            }
          }
        };

        // Traverse the graph starting from the `in`.
        visitState(this.in);

        // Append epsilon-closure column.
        visited.forEach(function (state) {
          delete _this._transitionTable[state.number][EPSILON];
          _this._transitionTable[state.number][EPSILON_CLOSURE] = [].concat(_toConsumableArray(state.getEpsilonClosure())).map(function (s) {
            return s.number;
          });
        });
      }

      return this._transitionTable;
    }
  }]);

  return NFA;
}();

module.exports = NFA;
},{"../special-symbols":25}],25:[function(require,module,exports){
/**
 * The MIT License (MIT)
 * Copyright (c) 2017-present Dmitry Soshnikov <dmitry.soshnikov@gmail.com>
 */

'use strict';

/**
 * Epsilon, the empty string.
 */

var EPSILON = 'ε';

/**
 * Epsilon-closure.
 */
var EPSILON_CLOSURE = EPSILON + '*';

module.exports = {
  EPSILON: EPSILON,
  EPSILON_CLOSURE: EPSILON_CLOSURE
};
},{}],26:[function(require,module,exports){
/**
 * The MIT License (MIT)
 * Copyright (c) 2017-present Dmitry Soshnikov <dmitry.soshnikov@gmail.com>
 */

'use strict';

/**
 * A generic FA State class (base for NFA and DFA).
 *
 * Maintains the transition map, and the flag whether
 * the state is accepting.
 */

var _createClass = function () { function defineProperties(target, props) { for (var i = 0; i < props.length; i++) { var descriptor = props[i]; descriptor.enumerable = descriptor.enumerable || false; descriptor.configurable = true; if ("value" in descriptor) descriptor.writable = true; Object.defineProperty(target, descriptor.key, descriptor); } } return function (Constructor, protoProps, staticProps) { if (protoProps) defineProperties(Constructor.prototype, protoProps); if (staticProps) defineProperties(Constructor, staticProps); return Constructor; }; }();

function _classCallCheck(instance, Constructor) { if (!(instance instanceof Constructor)) { throw new TypeError("Cannot call a class as a function"); } }

var State = function () {
  function State() {
    var _ref = arguments.length > 0 && arguments[0] !== undefined ? arguments[0] : {},
        _ref$accepting = _ref.accepting,
        accepting = _ref$accepting === undefined ? false : _ref$accepting;

    _classCallCheck(this, State);

    /**
     * Outgoing transitions to other states.
     */
    this._transitions = new Map();

    /**
     * Whether the state is accepting.
     */
    this.accepting = accepting;
  }

  /**
   * Returns transitions for this state.
   */


  _createClass(State, [{
    key: 'getTransitions',
    value: function getTransitions() {
      return this._transitions;
    }

    /**
     * Creates a transition on symbol.
     */

  }, {
    key: 'addTransition',
    value: function addTransition(symbol, toState) {
      this.getTransitionsOnSymbol(symbol).add(toState);
      return this;
    }

    /**
     * Returns transitions set on symbol.
     */

  }, {
    key: 'getTransitionsOnSymbol',
    value: function getTransitionsOnSymbol(symbol) {
      var transitions = this._transitions.get(symbol);

      if (!transitions) {
        transitions = new Set();
        this._transitions.set(symbol, transitions);
      }

      return transitions;
    }
  }]);

  return State;
}();

module.exports = State;
},{}],27:[function(require,module,exports){
/**
 * The MIT License (MIT)
 * Copyright (c) 2017-present Dmitry Soshnikov <dmitry.soshnikov@gmail.com>
 */

'use strict';

var clone = require('../utils/clone');
var parser = require('../parser');
var transform = require('../transform');
var optimizationTransforms = require('./transforms');

module.exports = {
  /**
   * Optimizer transforms a regular expression into an optimized version,
   * replacing some sub-expressions with their idiomatic patterns.
   *
   * @param string | RegExp | AST - a regexp to optimize.
   *
   * @return TransformResult - an optimized regexp.
   *
   * Example:
   *
   *   /[a-zA-Z_0-9][a-zA-Z_0-9]*\e{1,}/
   *
   * Optimized to:
   *
   *   /\w+e+/
   */
  optimize: function optimize(regexp) {
    var _ref = arguments.length > 1 && arguments[1] !== undefined ? arguments[1] : {},
        _ref$whitelist = _ref.whitelist,
        whitelist = _ref$whitelist === undefined ? [] : _ref$whitelist,
        _ref$blacklist = _ref.blacklist,
        blacklist = _ref$blacklist === undefined ? [] : _ref$blacklist;

    var transformsRaw = whitelist.length > 0 ? whitelist : Array.from(optimizationTransforms.keys());

    var transformToApply = transformsRaw.filter(function (transform) {
      return !blacklist.includes(transform);
    });

    var ast = regexp;
    if (regexp instanceof RegExp) {
      regexp = '' + regexp;
    }

    if (typeof regexp === 'string') {
      ast = parser.parse(regexp);
    }

    var result = new transform.TransformResult(ast);
    var prevResultString = void 0;

    do {
      // Get a copy of the current state here so
      // we can compare it with the state at the
      // end of the loop.
      prevResultString = result.toString();
      ast = clone(result.getAST());

      transformToApply.forEach(function (transformName) {
        if (!optimizationTransforms.has(transformName)) {
          throw new Error('Unknown optimization-transform: ' + transformName + '. ' + 'Available transforms are: ' + Array.from(optimizationTransforms.keys()).join(', '));
        }

        var transformer = optimizationTransforms.get(transformName);

        // Don't override result just yet since we
        // might want to rollback the transform
        var newResult = transform.transform(ast, transformer);

        if (newResult.toString() !== result.toString()) {
          if (newResult.toString().length <= result.toString().length) {
            result = newResult;
          } else {
            // Result has changed but is not shorter:
            // restore ast to its previous state.

            ast = clone(result.getAST());
          }
        }
      });

      // Keep running the optimizer until it stops
      // making any change to the regexp.
    } while (result.toString() !== prevResultString);

    return result;
  }
};
},{"../parser":46,"../transform":49,"../utils/clone":53,"./transforms":40}],28:[function(require,module,exports){
/**
 * The MIT License (MIT)
 * Copyright (c) 2017-present Dmitry Soshnikov <dmitry.soshnikov@gmail.com>
 */

'use strict';

var UPPER_A_CP = 'A'.codePointAt(0);
var UPPER_Z_CP = 'Z'.codePointAt(0);
/**
 * Transforms case-insensitive regexp to lowercase
 *
 * /AaBbÏ/i -> /aabbï/i
 */
module.exports = {
  _AZClassRanges: null,
  _hasUFlag: false,
  init: function init(ast) {
    this._AZClassRanges = new Set();
    this._hasUFlag = ast.flags.includes('u');
  },
  shouldRun: function shouldRun(ast) {
    return ast.flags.includes('i');
  },
  Char: function Char(path) {
    var node = path.node,
        parent = path.parent;

    if (isNaN(node.codePoint)) {
      return;
    }

    // Engine support for case-insensitive matching without the u flag
    // for characters above \u1000 does not seem reliable.
    if (!this._hasUFlag && node.codePoint >= 0x1000) {
      return;
    }

    if (parent.type === 'ClassRange') {
      // The only class ranges we handle must be inside A-Z.
      // After the `from` char is processed, the isAZClassRange test
      // will be false, so we use a Set to keep track of parents and
      // process the `to` char.
      if (!this._AZClassRanges.has(parent) && !isAZClassRange(parent)) {
        return;
      }
      this._AZClassRanges.add(parent);
    }

    var lower = node.symbol.toLowerCase();
    if (lower !== node.symbol) {
      node.value = displaySymbolAsValue(lower, node);
      node.symbol = lower;
      node.codePoint = lower.codePointAt(0);
    }
  }
};

function isAZClassRange(classRange) {
  var from = classRange.from,
      to = classRange.to;
  // A-Z

  return from.codePoint >= UPPER_A_CP && from.codePoint <= UPPER_Z_CP && to.codePoint >= UPPER_A_CP && to.codePoint <= UPPER_Z_CP;
}

function displaySymbolAsValue(symbol, node) {
  var codePoint = symbol.codePointAt(0);
  if (node.kind === 'decimal') {
    return '\\' + codePoint;
  }
  if (node.kind === 'oct') {
    return '\\0' + codePoint.toString(8);
  }
  if (node.kind === 'hex') {
    return '\\x' + codePoint.toString(16);
  }
  if (node.kind === 'unicode') {
    if (node.isSurrogatePair) {
      var _getSurrogatePairFrom = getSurrogatePairFromCodePoint(codePoint),
          lead = _getSurrogatePairFrom.lead,
          trail = _getSurrogatePairFrom.trail;

      return '\\u' + '0'.repeat(4 - lead.length) + lead + '\\u' + '0'.repeat(4 - trail.length) + trail;
    } else if (node.value.includes('{')) {
      return '\\u{' + codePoint.toString(16) + '}';
    } else {
      var code = codePoint.toString(16);
      return '\\u' + '0'.repeat(4 - code.length) + code;
    }
  }
  // simple
  return symbol;
}

/**
 * Converts a code point to a surrogate pair.
 * Conversion algorithm is taken from The Unicode Standard 3.0 Section 3.7
 * (https://www.unicode.org/versions/Unicode3.0.0/ch03.pdf)
 * @param {number} codePoint - Between 0x10000 and 0x10ffff
 * @returns {{lead: string, trail: string}}
 */
function getSurrogatePairFromCodePoint(codePoint) {
  var lead = Math.floor((codePoint - 0x10000) / 0x400) + 0xd800;
  var trail = (codePoint - 0x10000) % 0x400 + 0xdc00;
  return {
    lead: lead.toString(16),
    trail: trail.toString(16)
  };
}
},{}],29:[function(require,module,exports){
/**
 * The MIT License (MIT)
 * Copyright (c) 2017-present Dmitry Soshnikov <dmitry.soshnikov@gmail.com>
 */

'use strict';

/**
 * A regexp-tree plugin to merge class ranges.
 *
 * [a-ec] -> [a-e]
 * [a-ec-e] -> [a-e]
 * [\w\da-f] -> [\w]
 * [abcdef] -> [a-f]
 */

module.exports = {
  _hasIUFlags: false,
  init: function init(ast) {
    this._hasIUFlags = ast.flags.includes('i') && ast.flags.includes('u');
  },
  CharacterClass: function CharacterClass(path) {
    var node = path.node;

    var expressions = node.expressions;

    var metas = [];
    // Extract metas
    expressions.forEach(function (expression) {
      if (isMeta(expression)) {
        metas.push(expression.value);
      }
    });

    expressions.sort(sortCharClass);

    for (var i = 0; i < expressions.length; i++) {
      var expression = expressions[i];
      if (fitsInMetas(expression, metas, this._hasIUFlags) || combinesWithPrecedingClassRange(expression, expressions[i - 1]) || combinesWithFollowingClassRange(expression, expressions[i + 1])) {
        expressions.splice(i, 1);
        i--;
      } else {
        var nbMergedChars = charCombinesWithPrecedingChars(expression, i, expressions);
        expressions.splice(i - nbMergedChars + 1, nbMergedChars);
        i -= nbMergedChars;
      }
    }
  }
};

/**
 * Sorts expressions in char class in the following order:
 * - meta chars, ordered alphabetically by value
 * - chars (except `control` kind) and class ranges, ordered alphabetically (`from` char is used for class ranges)
 * - if ambiguous, class range comes before char
 * - if ambiguous between two class ranges, orders alphabetically by `to` char
 * - control chars, ordered alphabetically by value
 * @param {Object} a - Left Char or ClassRange node
 * @param {Object} b - Right Char or ClassRange node
 * @returns {number}
 */
function sortCharClass(a, b) {
  var aValue = getSortValue(a);
  var bValue = getSortValue(b);

  if (aValue === bValue) {
    // We want ClassRange before Char
    // [bb-d] -> [b-db]
    if (a.type === 'ClassRange' && b.type !== 'ClassRange') {
      return -1;
    }
    if (b.type === 'ClassRange' && a.type !== 'ClassRange') {
      return 1;
    }
    if (a.type === 'ClassRange' && b.type === 'ClassRange') {
      return getSortValue(a.to) - getSortValue(b.to);
    }
    if (isMeta(a) && isMeta(b) || isControl(a) && isControl(b)) {
      return a.value < b.value ? -1 : 1;
    }
  }
  return aValue - bValue;
}

/**
 * @param {Object} expression - Char or ClassRange node
 * @returns {number}
 */
function getSortValue(expression) {
  if (expression.type === 'Char') {
    if (expression.value === '-') {
      return Infinity;
    }
    if (expression.kind === 'control') {
      return Infinity;
    }
    if (expression.kind === 'meta' && isNaN(expression.codePoint)) {
      return -1;
    }
    return expression.codePoint;
  }
  // ClassRange
  return expression.from.codePoint;
}

/**
 * Checks if a node is a meta char from the set \d\w\s\D\W\S
 * @param {Object} expression - Char or ClassRange node
 * @param {?string} value
 * @returns {boolean}
 */
function isMeta(expression) {
  var value = arguments.length > 1 && arguments[1] !== undefined ? arguments[1] : null;

  return expression.type === 'Char' && expression.kind === 'meta' && (value ? expression.value === value : /^\\[dws]$/i.test(expression.value));
}

/**
 * @param {Object} expression - Char or ClassRange node
 * @returns {boolean}
 */
function isControl(expression) {
  return expression.type === 'Char' && expression.kind === 'control';
}

/**
 * @param {Object} expression - Char or ClassRange node
 * @param {string[]} metas - Array of meta chars, e.g. ["\\w", "\\s"]
 * @param {boolean} hasIUFlags
 * @returns {boolean}
 */
function fitsInMetas(expression, metas, hasIUFlags) {
  for (var i = 0; i < metas.length; i++) {
    if (fitsInMeta(expression, metas[i], hasIUFlags)) {
      return true;
    }
  }
  return false;
}

/**
 * @param {Object} expression - Char or ClassRange node
 * @param {string} meta - e.g. "\\w"
 * @param {boolean} hasIUFlags
 * @returns {boolean}
 */
function fitsInMeta(expression, meta, hasIUFlags) {
  if (expression.type === 'ClassRange') {
    return fitsInMeta(expression.from, meta, hasIUFlags) && fitsInMeta(expression.to, meta, hasIUFlags);
  }

  // Special cases:
  // \S contains \w and \d
  if (meta === '\\S' && (isMeta(expression, '\\w') || isMeta(expression, '\\d'))) {
    return true;
  }
  // \D contains \W and \s
  if (meta === '\\D' && (isMeta(expression, '\\W') || isMeta(expression, '\\s'))) {
    return true;
  }
  // \w contains \d
  if (meta === '\\w' && isMeta(expression, '\\d')) {
    return true;
  }
  // \W contains \s
  if (meta === '\\W' && isMeta(expression, '\\s')) {
    return true;
  }

  if (expression.type !== 'Char' || isNaN(expression.codePoint)) {
    return false;
  }

  if (meta === '\\s') {
    return fitsInMetaS(expression);
  }
  if (meta === '\\S') {
    return !fitsInMetaS(expression);
  }
  if (meta === '\\d') {
    return fitsInMetaD(expression);
  }
  if (meta === '\\D') {
    return !fitsInMetaD(expression);
  }
  if (meta === '\\w') {
    return fitsInMetaW(expression, hasIUFlags);
  }
  if (meta === '\\W') {
    return !fitsInMetaW(expression, hasIUFlags);
  }
  return false;
}

/**
 * @param {Object} expression - Char node with codePoint
 * @returns {boolean}
 */
function fitsInMetaS(expression) {
  return expression.codePoint === 0x0009 || // \t
  expression.codePoint === 0x000a || // \n
  expression.codePoint === 0x000b || // \v
  expression.codePoint === 0x000c || // \f
  expression.codePoint === 0x000d || // \r
  expression.codePoint === 0x0020 || // space
  expression.codePoint === 0x00a0 || // nbsp
  expression.codePoint === 0x1680 || // part of Zs
  expression.codePoint >= 0x2000 && expression.codePoint <= 0x200a || // part of Zs
  expression.codePoint === 0x2028 || // line separator
  expression.codePoint === 0x2029 || // paragraph separator
  expression.codePoint === 0x202f || // part of Zs
  expression.codePoint === 0x205f || // part of Zs
  expression.codePoint === 0x3000 || // part of Zs
  expression.codePoint === 0xfeff; // zwnbsp
}

/**
 * @param {Object} expression - Char node with codePoint
 * @returns {boolean}
 */
function fitsInMetaD(expression) {
  return expression.codePoint >= 0x30 && expression.codePoint <= 0x39; // 0-9
}

/**
 * @param {Object} expression - Char node with codePoint
 * @param {boolean} hasIUFlags
 * @returns {boolean}
 */
function fitsInMetaW(expression, hasIUFlags) {
  return fitsInMetaD(expression) || expression.codePoint >= 0x41 && expression.codePoint <= 0x5a || // A-Z
  expression.codePoint >= 0x61 && expression.codePoint <= 0x7a || // a-z
  expression.value === '_' || hasIUFlags && (expression.codePoint === 0x017f || expression.codePoint === 0x212a);
}

/**
 * @param {Object} expression - Char or ClassRange node
 * @param {Object} classRange - Char or ClassRange node
 * @returns {boolean}
 */
function combinesWithPrecedingClassRange(expression, classRange) {
  if (classRange && classRange.type === 'ClassRange') {
    if (fitsInClassRange(expression, classRange)) {
      // [a-gc] -> [a-g]
      // [a-gc-e] -> [a-g]
      return true;
    } else if (
    // We only want \w chars or char codes to keep readability
    isMetaWCharOrCode(expression) && classRange.to.codePoint === expression.codePoint - 1) {
      // [a-de] -> [a-e]
      classRange.to = expression;
      return true;
    } else if (expression.type === 'ClassRange' && expression.from.codePoint <= classRange.to.codePoint + 1 && expression.to.codePoint >= classRange.from.codePoint - 1) {
      // [a-db-f] -> [a-f]
      // [b-fa-d] -> [a-f]
      // [a-cd-f] -> [a-f]
      if (expression.from.codePoint < classRange.from.codePoint) {
        classRange.from = expression.from;
      }
      if (expression.to.codePoint > classRange.to.codePoint) {
        classRange.to = expression.to;
      }
      return true;
    }
  }
  return false;
}

/**
 * @param {Object} expression - Char or ClassRange node
 * @param {Object} classRange - Char or ClassRange node
 * @returns {boolean}
 */
function combinesWithFollowingClassRange(expression, classRange) {
  if (classRange && classRange.type === 'ClassRange') {
    // Considering the elements were ordered alphabetically,
    // there is only one case to handle
    // [ab-e] -> [a-e]
    if (
    // We only want \w chars or char codes to keep readability
    isMetaWCharOrCode(expression) && classRange.from.codePoint === expression.codePoint + 1) {
      classRange.from = expression;
      return true;
    }
  }

  return false;
}

/**
 * @param {Object} expression - Char or ClassRange node
 * @param {Object} classRange - ClassRange node
 * @returns {boolean}
 */
function fitsInClassRange(expression, classRange) {
  if (expression.type === 'Char' && isNaN(expression.codePoint)) {
    return false;
  }
  if (expression.type === 'ClassRange') {
    return fitsInClassRange(expression.from, classRange) && fitsInClassRange(expression.to, classRange);
  }
  return expression.codePoint >= classRange.from.codePoint && expression.codePoint <= classRange.to.codePoint;
}

/**
 * @param {Object} expression - Char or ClassRange node
 * @param {Number} index
 * @param {Object[]} expressions - expressions in CharClass
 * @returns {number} - Number of characters combined with expression
 */
function charCombinesWithPrecedingChars(expression, index, expressions) {
  // We only want \w chars or char codes to keep readability
  if (!isMetaWCharOrCode(expression)) {
    return 0;
  }
  var nbMergedChars = 0;
  while (index > 0) {
    var currentExpression = expressions[index];
    var precedingExpresion = expressions[index - 1];
    if (isMetaWCharOrCode(precedingExpresion) && precedingExpresion.codePoint === currentExpression.codePoint - 1) {
      nbMergedChars++;
      index--;
    } else {
      break;
    }
  }

  if (nbMergedChars > 1) {
    expressions[index] = {
      type: 'ClassRange',
      from: expressions[index],
      to: expression
    };
    return nbMergedChars;
  }
  return 0;
}

function isMetaWCharOrCode(expression) {
  return expression && expression.type === 'Char' && !isNaN(expression.codePoint) && (fitsInMetaW(expression, false) || expression.kind === 'unicode' || expression.kind === 'hex' || expression.kind === 'oct' || expression.kind === 'decimal');
}
},{}],30:[function(require,module,exports){
/**
 * The MIT License (MIT)
 * Copyright (c) 2017-present Dmitry Soshnikov <dmitry.soshnikov@gmail.com>
 */

'use strict';

/**
 * A regexp-tree plugin to simplify character classes
 * spanning only one or two chars.
 *
 * [a-a] -> [a]
 * [a-b] -> [ab]
 */

module.exports = {
  ClassRange: function ClassRange(path) {
    var node = path.node;


    if (node.from.codePoint === node.to.codePoint) {

      path.replace(node.from);
    } else if (node.from.codePoint === node.to.codePoint - 1) {

      path.getParent().insertChildAt(node.to, path.index + 1);
      path.replace(node.from);
    }
  }
};
},{}],31:[function(require,module,exports){
/**
 * The MIT License (MIT)
 * Copyright (c) 2017-present Dmitry Soshnikov <dmitry.soshnikov@gmail.com>
 */

'use strict';

/**
 * A regexp-tree plugin to remove duplicates from character classes.
 */

module.exports = {
  CharacterClass: function CharacterClass(path) {
    var node = path.node;

    var sources = {};

    for (var i = 0; i < node.expressions.length; i++) {
      var childPath = path.getChild(i);
      var source = childPath.jsonEncode();

      if (sources.hasOwnProperty(source)) {
        childPath.remove();

        // Since we remove the current node.
        // TODO: make it simpler for users with a method.
        i--;
      }

      sources[source] = true;
    }
  }
};
},{}],32:[function(require,module,exports){
/**
 * The MIT License (MIT)
 * Copyright (c) 2017-present Dmitry Soshnikov <dmitry.soshnikov@gmail.com>
 */

'use strict';

/**
 * A regexp-tree plugin to replace standard character classes with
 * their meta symbols equivalents.
 */

function _toConsumableArray(arr) { if (Array.isArray(arr)) { for (var i = 0, arr2 = Array(arr.length); i < arr.length; i++) { arr2[i] = arr[i]; } return arr2; } else { return Array.from(arr); } }

module.exports = {
  _hasIFlag: false,
  _hasUFlag: false,
  init: function init(ast) {
    this._hasIFlag = ast.flags.includes('i');
    this._hasUFlag = ast.flags.includes('u');
  },
  CharacterClass: function CharacterClass(path) {
    // [0-9] -> \d
    rewriteNumberRanges(path);

    // [a-zA-Z_0-9] -> \w
    rewriteWordRanges(path, this._hasIFlag, this._hasUFlag);

    // [ \f\n\r\t\v\u00a0\u1680\u2000-\u200a\u2028\u2029\u202f\u205f\u3000\ufeff] -> \s
    rewriteWhitespaceRanges(path);
  }
};

/**
 * Rewrites number ranges: [0-9] -> \d
 */
function rewriteNumberRanges(path) {
  var node = path.node;


  node.expressions.forEach(function (expression, i) {
    if (isFullNumberRange(expression)) {
      path.getChild(i).replace({
        type: 'Char',
        value: '\\d',
        kind: 'meta'
      });
    }
  });
}

/**
 * Rewrites word ranges: [a-zA-Z_0-9] -> \w
 * Thus, the ranges may go in any order, and other symbols/ranges
 * are kept untouched, e.g. [a-z_\dA-Z$] -> [\w$]
 */
function rewriteWordRanges(path, hasIFlag, hasUFlag) {
  var node = path.node;


  var numberPath = null;
  var lowerCasePath = null;
  var upperCasePath = null;
  var underscorePath = null;
  var u017fPath = null;
  var u212aPath = null;

  node.expressions.forEach(function (expression, i) {
    // \d
    if (isMetaChar(expression, '\\d')) {
      numberPath = path.getChild(i);
    }

    // a-z
    else if (isLowerCaseRange(expression)) {
        lowerCasePath = path.getChild(i);
      }

      // A-Z
      else if (isUpperCaseRange(expression)) {
          upperCasePath = path.getChild(i);
        }

        // _
        else if (isUnderscore(expression)) {
            underscorePath = path.getChild(i);
          } else if (hasIFlag && hasUFlag && isCodePoint(expression, 0x017f)) {
            u017fPath = path.getChild(i);
          } else if (hasIFlag && hasUFlag && isCodePoint(expression, 0x212a)) {
            u212aPath = path.getChild(i);
          }
  });

  // If we found the whole pattern, replace it.
  if (numberPath && (lowerCasePath && upperCasePath || hasIFlag && (lowerCasePath || upperCasePath)) && underscorePath && (!hasUFlag || !hasIFlag || u017fPath && u212aPath)) {
    // Put \w in place of \d.
    numberPath.replace({
      type: 'Char',
      value: '\\w',
      kind: 'meta'
    });

    // Other paths are removed.
    if (lowerCasePath) {
      lowerCasePath.remove();
    }
    if (upperCasePath) {
      upperCasePath.remove();
    }
    underscorePath.remove();
    if (u017fPath) {
      u017fPath.remove();
    }
    if (u212aPath) {
      u212aPath.remove();
    }
  }
}

/**
 * Rewrites whitespace ranges: [ \f\n\r\t\v\u00a0\u1680\u2000-\u200a\u2028\u2029\u202f\u205f\u3000\ufeff] -> \s.
 */
var whitespaceRangeTests = [function (node) {
  return isChar(node, ' ');
}].concat(_toConsumableArray(['\\f', '\\n', '\\r', '\\t', '\\v'].map(function (char) {
  return function (node) {
    return isMetaChar(node, char);
  };
})), _toConsumableArray([0x00a0, 0x1680, 0x2028, 0x2029, 0x202f, 0x205f, 0x3000, 0xfeff].map(function (codePoint) {
  return function (node) {
    return isCodePoint(node, codePoint);
  };
})), [function (node) {
  return node.type === 'ClassRange' && isCodePoint(node.from, 0x2000) && isCodePoint(node.to, 0x200a);
}]);

function rewriteWhitespaceRanges(path) {
  var node = path.node;


  if (node.expressions.length < whitespaceRangeTests.length || !whitespaceRangeTests.every(function (test) {
    return node.expressions.some(function (expression) {
      return test(expression);
    });
  })) {
    return;
  }

  // If we found the whole pattern, replace it.

  // Put \s in place of \n.
  var nNode = node.expressions.find(function (expression) {
    return isMetaChar(expression, '\\n');
  });
  nNode.value = '\\s';
  nNode.symbol = undefined;
  nNode.codePoint = NaN;

  // Other paths are removed.
  node.expressions.map(function (expression, i) {
    return whitespaceRangeTests.some(function (test) {
      return test(expression);
    }) ? path.getChild(i) : undefined;
  }).filter(Boolean).forEach(function (path) {
    return path.remove();
  });
}

function isFullNumberRange(node) {
  return node.type === 'ClassRange' && node.from.value === '0' && node.to.value === '9';
}

function isChar(node, value) {
  var kind = arguments.length > 2 && arguments[2] !== undefined ? arguments[2] : 'simple';

  return node.type === 'Char' && node.value === value && node.kind === kind;
}

function isMetaChar(node, value) {
  return isChar(node, value, 'meta');
}

function isLowerCaseRange(node) {
  return node.type === 'ClassRange' && node.from.value === 'a' && node.to.value === 'z';
}

function isUpperCaseRange(node) {
  return node.type === 'ClassRange' && node.from.value === 'A' && node.to.value === 'Z';
}

function isUnderscore(node) {
  return node.type === 'Char' && node.value === '_' && node.kind === 'simple';
}

function isCodePoint(node, codePoint) {
  return node.type === 'Char' && node.kind === 'unicode' && node.codePoint === codePoint;
}
},{}],33:[function(require,module,exports){
/**
 * The MIT License (MIT)
 * Copyright (c) 2017-present Dmitry Soshnikov <dmitry.soshnikov@gmail.com>
 */

'use strict';

/**
 * A regexp-tree plugin to replace single char character classes with
 * just that character.
 *
 * [\d] -> \d, [^\w] -> \W
 */

module.exports = {
  CharacterClass: function CharacterClass(path) {
    var node = path.node;


    if (node.expressions.length !== 1 || !hasAppropriateSiblings(path) || !isAppropriateChar(node.expressions[0])) {
      return;
    }

    var _node$expressions$ = node.expressions[0],
        value = _node$expressions$.value,
        kind = _node$expressions$.kind,
        escaped = _node$expressions$.escaped;


    if (node.negative) {
      // For negative can extract only meta chars like [^\w] -> \W
      // cannot do for [^a] -> a (wrong).
      if (!isMeta(value)) {
        return;
      }

      value = getInverseMeta(value);
    }

    path.replace({
      type: 'Char',
      value: value,
      kind: kind,
      escaped: escaped || shouldEscape(value)
    });
  }
};

function isAppropriateChar(node) {
  return node.type === 'Char' &&
  // We don't extract [\b] (backspace) since \b has different
  // semantics (word boundary).
  node.value !== '\\b';
}

function isMeta(value) {
  return (/^\\[dwsDWS]$/.test(value)
  );
}

function getInverseMeta(value) {
  return (/[dws]/.test(value) ? value.toUpperCase() : value.toLowerCase()
  );
}

function hasAppropriateSiblings(path) {
  var parent = path.parent,
      index = path.index;


  if (parent.type !== 'Alternative') {
    return true;
  }

  var previousNode = parent.expressions[index - 1];
  if (previousNode == null) {
    return true;
  }

  // Don't optimized \1[0] to \10
  if (previousNode.type === 'Backreference' && previousNode.kind === 'number') {
    return false;
  }

  // Don't optimized \2[0] to \20
  if (previousNode.type === 'Char' && previousNode.kind === 'decimal') {
    return false;
  }

  return true;
}

// Note: \{ and \} are always preserved to avoid `a[{]2[}]` turning
// into `a{2}`.
function shouldEscape(value) {
  return (/[*[()+?$./{}|]/.test(value)
  );
}
},{}],34:[function(require,module,exports){
/**
 * The MIT License (MIT)
 * Copyright (c) 2017-present Dmitry Soshnikov <dmitry.soshnikov@gmail.com>
 */

'use strict';

var UPPER_A_CP = 'A'.codePointAt(0);
var UPPER_Z_CP = 'Z'.codePointAt(0);
var LOWER_A_CP = 'a'.codePointAt(0);
var LOWER_Z_CP = 'z'.codePointAt(0);
var DIGIT_0_CP = '0'.codePointAt(0);
var DIGIT_9_CP = '9'.codePointAt(0);

/**
 * A regexp-tree plugin to transform coded chars into simple chars.
 *
 * \u0061 -> a
 */
module.exports = {
  Char: function Char(path) {
    var node = path.node,
        parent = path.parent;

    if (isNaN(node.codePoint) || node.kind === 'simple') {
      return;
    }

    if (parent.type === 'ClassRange') {
      if (!isSimpleRange(parent)) {
        return;
      }
    }

    if (!isPrintableASCIIChar(node.codePoint)) {
      return;
    }

    var symbol = String.fromCodePoint(node.codePoint);
    var newChar = {
      type: 'Char',
      kind: 'simple',
      value: symbol,
      symbol: symbol,
      codePoint: node.codePoint
    };
    if (needsEscape(symbol, parent.type)) {
      newChar.escaped = true;
    }
    path.replace(newChar);
  }
};

/**
 * Checks if a range is included either in 0-9, a-z or A-Z
 * @param classRange
 * @returns {boolean}
 */
function isSimpleRange(classRange) {
  var from = classRange.from,
      to = classRange.to;

  return from.codePoint >= DIGIT_0_CP && from.codePoint <= DIGIT_9_CP && to.codePoint >= DIGIT_0_CP && to.codePoint <= DIGIT_9_CP || from.codePoint >= UPPER_A_CP && from.codePoint <= UPPER_Z_CP && to.codePoint >= UPPER_A_CP && to.codePoint <= UPPER_Z_CP || from.codePoint >= LOWER_A_CP && from.codePoint <= LOWER_Z_CP && to.codePoint >= LOWER_A_CP && to.codePoint <= LOWER_Z_CP;
}

/**
 * Checks if a code point in the range of printable ASCII chars
 * (DEL char excluded)
 * @param codePoint
 * @returns {boolean}
 */
function isPrintableASCIIChar(codePoint) {
  return codePoint >= 0x20 && codePoint <= 0x7e;
}

function needsEscape(symbol, parentType) {
  if (parentType === 'ClassRange' || parentType === 'CharacterClass') {
    return (/[\]\\^-]/.test(symbol)
    );
  }

  return (/[*[()+?^$./\\|{}]/.test(symbol)
  );
}
},{}],35:[function(require,module,exports){
/**
 * The MIT License (MIT)
 * Copyright (c) 2017-present Dmitry Soshnikov <dmitry.soshnikov@gmail.com>
 */

'use strict';

/**
 * A regexp-tree plugin to remove unnecessary escape.
 *
 * \e -> e
 *
 * [\(] -> [(]
 */

module.exports = {
  _hasXFlag: false,
  init: function init(ast) {
    this._hasXFlag = ast.flags.includes('x');
  },
  Char: function Char(path) {
    var node = path.node;


    if (!node.escaped) {
      return;
    }

    if (shouldUnescape(path, this._hasXFlag)) {
      delete node.escaped;
    }
  }
};

function shouldUnescape(path, hasXFlag) {
  var value = path.node.value,
      index = path.index,
      parent = path.parent;

  // In char class (, etc are allowed.

  if (parent.type !== 'CharacterClass' && parent.type !== 'ClassRange') {
    return !preservesEscape(value, index, parent, hasXFlag);
  }

  return !preservesInCharClass(value, index, parent);
}

/**
 * \], \\, \^, \-
 */
function preservesInCharClass(value, index, parent) {
  if (value === '^') {
    // Avoid [\^a] turning into [^a]
    return index === 0 && !parent.negative;
  }
  if (value === '-') {
    // Avoid [a\-z] turning into [a-z]
    return true;
  }
  return (/[\]\\]/.test(value)
  );
}

function preservesEscape(value, index, parent, hasXFlag) {
  if (value === '{') {
    return preservesOpeningCurlyBraceEscape(index, parent);
  }

  if (value === '}') {
    return preservesClosingCurlyBraceEscape(index, parent);
  }

  if (hasXFlag && /[ #]/.test(value)) {
    return true;
  }

  return (/[*[()+?^$./\\|]/.test(value)
  );
}

function consumeNumbers(startIndex, parent, rtl) {
  var i = startIndex;
  var siblingNode = (rtl ? i >= 0 : i < parent.expressions.length) && parent.expressions[i];

  while (siblingNode && siblingNode.type === 'Char' && siblingNode.kind === 'simple' && !siblingNode.escaped && /\d/.test(siblingNode.value)) {
    rtl ? i-- : i++;
    siblingNode = (rtl ? i >= 0 : i < parent.expressions.length) && parent.expressions[i];
  }

  return Math.abs(startIndex - i);
}

function isSimpleChar(node, value) {
  return node && node.type === 'Char' && node.kind === 'simple' && !node.escaped && node.value === value;
}

function preservesOpeningCurlyBraceEscape(index, parent) {
  // (?:\{) -> (?:{)
  if (index == null) {
    return false;
  }

  var nbFollowingNumbers = consumeNumbers(index + 1, parent);
  var i = index + nbFollowingNumbers + 1;
  var nextSiblingNode = i < parent.expressions.length && parent.expressions[i];

  if (nbFollowingNumbers) {
    // Avoid \{3} turning into {3}
    if (isSimpleChar(nextSiblingNode, '}')) {
      return true;
    }

    if (isSimpleChar(nextSiblingNode, ',')) {
      nbFollowingNumbers = consumeNumbers(i + 1, parent);
      i = i + nbFollowingNumbers + 1;
      nextSiblingNode = i < parent.expressions.length && parent.expressions[i];

      // Avoid \{3,} turning into {3,}
      return isSimpleChar(nextSiblingNode, '}');
    }
  }
  return false;
}

function preservesClosingCurlyBraceEscape(index, parent) {
  // (?:\{) -> (?:{)
  if (index == null) {
    return false;
  }

  var nbPrecedingNumbers = consumeNumbers(index - 1, parent, true);
  var i = index - nbPrecedingNumbers - 1;
  var previousSiblingNode = i >= 0 && parent.expressions[i];

  // Avoid {3\} turning into {3}
  if (nbPrecedingNumbers && isSimpleChar(previousSiblingNode, '{')) {
    return true;
  }

  if (isSimpleChar(previousSiblingNode, ',')) {
    nbPrecedingNumbers = consumeNumbers(i - 1, parent, true);
    i = i - nbPrecedingNumbers - 1;
    previousSiblingNode = i < parent.expressions.length && parent.expressions[i];

    // Avoid {3,\} turning into {3,}
    return nbPrecedingNumbers && isSimpleChar(previousSiblingNode, '{');
  }
  return false;
}
},{}],36:[function(require,module,exports){
/**
 * The MIT License (MIT)
 * Copyright (c) 2017-present Dmitry Soshnikov <dmitry.soshnikov@gmail.com>
 */

'use strict';

/**
 * A regexp-tree plugin to transform surrogate pairs into single unicode code point
 *
 * \ud83d\ude80 -> \u{1f680}
 */

module.exports = {
  shouldRun: function shouldRun(ast) {
    return ast.flags.includes('u');
  },
  Char: function Char(path) {
    var node = path.node;

    if (node.kind !== 'unicode' || !node.isSurrogatePair || isNaN(node.codePoint)) {
      return;
    }
    node.value = '\\u{' + node.codePoint.toString(16) + '}';
    delete node.isSurrogatePair;
  }
};
},{}],37:[function(require,module,exports){
/**
 * The MIT License (MIT)
 * Copyright (c) 2017-present Dmitry Soshnikov <dmitry.soshnikov@gmail.com>
 */

'use strict';

function _toConsumableArray(arr) { if (Array.isArray(arr)) { for (var i = 0, arr2 = Array(arr.length); i < arr.length; i++) { arr2[i] = arr[i]; } return arr2; } else { return Array.from(arr); } }

var NodePath = require('../../traverse/node-path');

var _require = require('../../transform/utils'),
    increaseQuantifierByOne = _require.increaseQuantifierByOne;

/**
 * A regexp-tree plugin to combine repeating patterns.
 *
 * /^abcabcabc/ -> /^abc{3}/
 * /^(?:abc){2}abc/ -> /^(?:abc){3}/
 * /^abc(?:abc){2}/ -> /^(?:abc){3}/
 */

module.exports = {
  Alternative: function Alternative(path) {
    var node = path.node;

    // We can skip the first child

    var index = 1;
    while (index < node.expressions.length) {
      var child = path.getChild(index);
      index = Math.max(1, combineRepeatingPatternLeft(path, child, index));

      if (index >= node.expressions.length) {
        break;
      }

      child = path.getChild(index);
      index = Math.max(1, combineWithPreviousRepetition(path, child, index));

      if (index >= node.expressions.length) {
        break;
      }

      child = path.getChild(index);
      index = Math.max(1, combineRepetitionWithPrevious(path, child, index));

      index++;
    }
  }
};

// abcabc -> (?:abc){2}
function combineRepeatingPatternLeft(alternative, child, index) {
  var node = alternative.node;


  var nbPossibleLengths = Math.ceil(index / 2);
  var i = 0;

  while (i < nbPossibleLengths) {
    var startIndex = index - 2 * i - 1;
    var right = void 0,
        left = void 0;

    if (i === 0) {
      right = child;
      left = alternative.getChild(startIndex);
    } else {
      right = NodePath.getForNode({
        type: 'Alternative',
        expressions: [].concat(_toConsumableArray(node.expressions.slice(index - i, index)), [child.node])
      });

      left = NodePath.getForNode({
        type: 'Alternative',
        expressions: [].concat(_toConsumableArray(node.expressions.slice(startIndex, index - i)))
      });
    }

    if (right.hasEqualSource(left)) {
      for (var j = 0; j < 2 * i + 1; j++) {
        alternative.getChild(startIndex).remove();
      }

      child.replace({
        type: 'Repetition',
        expression: i === 0 && right.node.type !== 'Repetition' ? right.node : {
          type: 'Group',
          capturing: false,
          expression: right.node
        },
        quantifier: {
          type: 'Quantifier',
          kind: 'Range',
          from: 2,
          to: 2,
          greedy: true
        }
      });
      return startIndex;
    }

    i++;
  }

  return index;
}

// (?:abc){2}abc -> (?:abc){3}
function combineWithPreviousRepetition(alternative, child, index) {
  var node = alternative.node;


  var i = 0;
  while (i < index) {
    var previousChild = alternative.getChild(i);

    if (previousChild.node.type === 'Repetition' && previousChild.node.quantifier.greedy) {
      var left = previousChild.getChild();
      var right = void 0;

      if (left.node.type === 'Group' && !left.node.capturing) {
        left = left.getChild();
      }

      if (i + 1 === index) {
        right = child;
        if (right.node.type === 'Group' && !right.node.capturing) {
          right = right.getChild();
        }
      } else {
        right = NodePath.getForNode({
          type: 'Alternative',
          expressions: [].concat(_toConsumableArray(node.expressions.slice(i + 1, index + 1)))
        });
      }

      if (left.hasEqualSource(right)) {
        for (var j = i; j < index; j++) {
          alternative.getChild(i + 1).remove();
        }

        increaseQuantifierByOne(previousChild.node.quantifier);

        return i;
      }
    }

    i++;
  }
  return index;
}

// abc(?:abc){2} -> (?:abc){3}
function combineRepetitionWithPrevious(alternative, child, index) {
  var node = alternative.node;


  if (child.node.type === 'Repetition' && child.node.quantifier.greedy) {
    var right = child.getChild();
    var left = void 0;

    if (right.node.type === 'Group' && !right.node.capturing) {
      right = right.getChild();
    }

    var rightLength = void 0;
    if (right.node.type === 'Alternative') {
      rightLength = right.node.expressions.length;
      left = NodePath.getForNode({
        type: 'Alternative',
        expressions: [].concat(_toConsumableArray(node.expressions.slice(index - rightLength, index)))
      });
    } else {
      rightLength = 1;
      left = alternative.getChild(index - 1);
      if (left.node.type === 'Group' && !left.node.capturing) {
        left = left.getChild();
      }
    }

    if (left.hasEqualSource(right)) {
      for (var j = index - rightLength; j < index; j++) {
        alternative.getChild(index - rightLength).remove();
      }

      increaseQuantifierByOne(child.node.quantifier);

      return index - rightLength;
    }
  }
  return index;
}
},{"../../transform/utils":50,"../../traverse/node-path":52}],38:[function(require,module,exports){
/**
 * The MIT License (MIT)
 * Copyright (c) 2017-present Dmitry Soshnikov <dmitry.soshnikov@gmail.com>
 */

'use strict';

var NodePath = require('../../traverse/node-path');

var _require = require('../../transform/utils'),
    disjunctionToList = _require.disjunctionToList,
    listToDisjunction = _require.listToDisjunction;

/**
 * Removes duplicates from a disjunction sequence:
 *
 * /(ab|bc|ab)+(xy|xy)+/ -> /(ab|bc)+(xy)+/
 */


module.exports = {
  Disjunction: function Disjunction(path) {
    var node = path.node;

    // Make unique nodes.

    var uniqueNodesMap = {};

    var parts = disjunctionToList(node).filter(function (part) {
      var encoded = part ? NodePath.getForNode(part).jsonEncode() : 'null';

      // Already recorded this part, filter out.
      if (uniqueNodesMap.hasOwnProperty(encoded)) {
        return false;
      }

      uniqueNodesMap[encoded] = part;
      return true;
    });

    // Replace with the optimized disjunction.
    path.replace(listToDisjunction(parts));
  }
};
},{"../../transform/utils":50,"../../traverse/node-path":52}],39:[function(require,module,exports){
/**
 * The MIT License (MIT)
 * Copyright (c) 2017-present Dmitry Soshnikov <dmitry.soshnikov@gmail.com>
 */

'use strict';

/**
 * A regexp-tree plugin to replace single char group disjunction to char group
 *
 * a|b|c -> [abc]
 * [12]|3|4 -> [1234]
 * (a|b|c) -> ([abc])
 * (?:a|b|c) -> [abc]
 */

module.exports = {
  Disjunction: function Disjunction(path) {
    var node = path.node,
        parent = path.parent;


    if (!handlers[parent.type]) {
      return;
    }

    var charset = new Map();

    if (!shouldProcess(node, charset) || !charset.size) {
      return;
    }

    var characterClass = {
      type: 'CharacterClass',
      expressions: Array.from(charset.keys()).sort().map(function (key) {
        return charset.get(key);
      })
    };

    handlers[parent.type](path.getParent(), characterClass);
  }
};

var handlers = {
  RegExp: function RegExp(path, characterClass) {
    var node = path.node;


    node.body = characterClass;
  },
  Group: function Group(path, characterClass) {
    var node = path.node;


    if (node.capturing) {
      node.expression = characterClass;
    } else {
      path.replace(characterClass);
    }
  }
};

function shouldProcess(expression, charset) {
  if (!expression) {
    // Abort on empty disjunction part
    return false;
  }

  var type = expression.type;


  if (type === 'Disjunction') {
    var left = expression.left,
        right = expression.right;


    return shouldProcess(left, charset) && shouldProcess(right, charset);
  } else if (type === 'Char') {
    var value = expression.value;


    charset.set(value, expression);

    return true;
  } else if (type === 'CharacterClass' && !expression.negative) {
    return expression.expressions.every(function (expression) {
      return shouldProcess(expression, charset);
    });
  }

  return false;
}
},{}],40:[function(require,module,exports){
/**
 * The MIT License (MIT)
 * Copyright (c) 2017-present Dmitry Soshnikov <dmitry.soshnikov@gmail.com>
 */

'use strict';

module.exports = new Map([
// \ud83d\ude80 -> \u{1f680}
['charSurrogatePairToSingleUnicode', require('./char-surrogate-pair-to-single-unicode-transform')],

// \u0061 -> a
['charCodeToSimpleChar', require('./char-code-to-simple-char-transform')],

// /Aa/i -> /aa/i
['charCaseInsensitiveLowerCaseTransform', require('./char-case-insensitive-lowercase-transform')],

// [\d\d] -> [\d]
['charClassRemoveDuplicates', require('./char-class-remove-duplicates-transform')],

// a{1,2}a{2,3} -> a{3,5}
['quantifiersMerge', require('./quantifiers-merge-transform')],

// a{1,} -> a+, a{3,3} -> a{3}, a{1} -> a
['quantifierRangeToSymbol', require('./quantifier-range-to-symbol-transform')],

// [a-a] -> [a], [a-b] -> [ab]
['charClassClassrangesToChars', require('./char-class-classranges-to-chars-transform')],

// [0-9] -> [\d]
['charClassToMeta', require('./char-class-to-meta-transform')],

// [\d] -> \d, [^\w] -> \W
['charClassToSingleChar', require('./char-class-to-single-char-transform')],

// \e -> e
['charEscapeUnescape', require('./char-escape-unescape-transform')],

// [a-de-f] -> [a-f]
['charClassClassrangesMerge', require('./char-class-classranges-merge-transform')],

// (ab|ab) -> (ab)
['disjunctionRemoveDuplicates', require('./disjunction-remove-duplicates-transform')],

// (a|b|c) -> [abc]
['groupSingleCharsToCharClass', require('./group-single-chars-to-char-class')],

// (?:)a -> a
['removeEmptyGroup', require('./remove-empty-group-transform')],

// (?:a) -> a
['ungroup', require('./ungroup-transform')],

// abcabcabc -> (?:abc){3}
['combineRepeatingPatterns', require('./combine-repeating-patterns-transform')]]);
},{"./char-case-insensitive-lowercase-transform":28,"./char-class-classranges-merge-transform":29,"./char-class-classranges-to-chars-transform":30,"./char-class-remove-duplicates-transform":31,"./char-class-to-meta-transform":32,"./char-class-to-single-char-transform":33,"./char-code-to-simple-char-transform":34,"./char-escape-unescape-transform":35,"./char-surrogate-pair-to-single-unicode-transform":36,"./combine-repeating-patterns-transform":37,"./disjunction-remove-duplicates-transform":38,"./group-single-chars-to-char-class":39,"./quantifier-range-to-symbol-transform":41,"./quantifiers-merge-transform":42,"./remove-empty-group-transform":43,"./ungroup-transform":44}],41:[function(require,module,exports){
/**
 * The MIT License (MIT)
 * Copyright (c) 2017-present Dmitry Soshnikov <dmitry.soshnikov@gmail.com>
 */

'use strict';

/**
 * A regexp-tree plugin to replace different range-based quantifiers
 * with their symbol equivalents.
 *
 * a{0,} -> a*
 * a{1,} -> a+
 * a{1} -> a
 *
 * NOTE: the following is automatically handled in the generator:
 *
 * a{3,3} -> a{3}
 */

module.exports = {
  Quantifier: function Quantifier(path) {
    var node = path.node;


    if (node.kind !== 'Range') {
      return;
    }

    // a{0,} -> a*
    rewriteOpenZero(path);

    // a{1,} -> a+
    rewriteOpenOne(path);

    // a{1} -> a
    rewriteExactOne(path);
  }
};

function rewriteOpenZero(path) {
  var node = path.node;


  if (node.from !== 0 || node.to) {
    return;
  }

  node.kind = '*';
  delete node.from;
}

function rewriteOpenOne(path) {
  var node = path.node;


  if (node.from !== 1 || node.to) {
    return;
  }

  node.kind = '+';
  delete node.from;
}

function rewriteExactOne(path) {
  var node = path.node;


  if (node.from !== 1 || node.to !== 1) {
    return;
  }

  path.parentPath.replace(path.parentPath.node.expression);
}
},{}],42:[function(require,module,exports){
/**
 * The MIT License (MIT)
 * Copyright (c) 2017-present Dmitry Soshnikov <dmitry.soshnikov@gmail.com>
 */

'use strict';

var _require = require('../../transform/utils'),
    increaseQuantifierByOne = _require.increaseQuantifierByOne;

/**
 * A regexp-tree plugin to merge quantifiers
 *
 * a+a+ -> a{2,}
 * a{2}a{3} -> a{5}
 * a{1,2}a{2,3} -> a{3,5}
 */


module.exports = {
  Repetition: function Repetition(path) {
    var node = path.node,
        parent = path.parent;


    if (parent.type !== 'Alternative' || !path.index) {
      return;
    }

    var previousSibling = path.getPreviousSibling();

    if (!previousSibling) {
      return;
    }

    if (previousSibling.node.type === 'Repetition') {
      if (!previousSibling.getChild().hasEqualSource(path.getChild())) {
        return;
      }

      var _extractFromTo = extractFromTo(previousSibling.node.quantifier),
          previousSiblingFrom = _extractFromTo.from,
          previousSiblingTo = _extractFromTo.to;

      var _extractFromTo2 = extractFromTo(node.quantifier),
          nodeFrom = _extractFromTo2.from,
          nodeTo = _extractFromTo2.to;

      // It's does not seem reliable to merge quantifiers with different greediness
      // when none of both is a greedy open range


      if (previousSibling.node.quantifier.greedy !== node.quantifier.greedy && !isGreedyOpenRange(previousSibling.node.quantifier) && !isGreedyOpenRange(node.quantifier)) {
        return;
      }

      // a*a* -> a*
      // a*a+ -> a+
      // a+a+ -> a{2,}
      // a{2}a{4} -> a{6}
      // a{1,2}a{2,3} -> a{3,5}
      // a{1,}a{2,} -> a{3,}
      // a+a{2,} -> a{3,}

      // a??a{2,} -> a{2,}
      // a*?a{2,} -> a{2,}
      // a+?a{2,} -> a{3,}

      node.quantifier.kind = 'Range';
      node.quantifier.from = previousSiblingFrom + nodeFrom;
      if (previousSiblingTo && nodeTo) {
        node.quantifier.to = previousSiblingTo + nodeTo;
      } else {
        delete node.quantifier.to;
      }
      if (isGreedyOpenRange(previousSibling.node.quantifier) || isGreedyOpenRange(node.quantifier)) {
        node.quantifier.greedy = true;
      }

      previousSibling.remove();
    } else {
      if (!previousSibling.hasEqualSource(path.getChild())) {
        return;
      }

      increaseQuantifierByOne(node.quantifier);
      previousSibling.remove();
    }
  }
};

function isGreedyOpenRange(quantifier) {
  return quantifier.greedy && (quantifier.kind === '+' || quantifier.kind === '*' || quantifier.kind === 'Range' && !quantifier.to);
}

function extractFromTo(quantifier) {
  var from = void 0,
      to = void 0;
  if (quantifier.kind === '*') {
    from = 0;
  } else if (quantifier.kind === '+') {
    from = 1;
  } else if (quantifier.kind === '?') {
    from = 0;
    to = 1;
  } else {
    from = quantifier.from;
    if (quantifier.to) {
      to = quantifier.to;
    }
  }
  return { from: from, to: to };
}
},{"../../transform/utils":50}],43:[function(require,module,exports){
/**
 * The MIT License (MIT)
 * Copyright (c) 2017-present Dmitry Soshnikov <dmitry.soshnikov@gmail.com>
 */

'use strict';

/**
 * A regexp-tree plugin to remove non-capturing empty groups.
 *
 * /(?:)a/ -> /a/
 * /a|(?:)/ -> /a|/
 */

module.exports = {
  Group: function Group(path) {
    var node = path.node,
        parent = path.parent;

    var childPath = path.getChild();

    if (node.capturing || childPath) {
      return;
    }

    if (parent.type === 'Repetition') {

      path.getParent().replace(node);
    } else if (parent.type !== 'RegExp') {

      path.remove();
    }
  }
};
},{}],44:[function(require,module,exports){
/**
 * The MIT License (MIT)
 * Copyright (c) 2017-present Dmitry Soshnikov <dmitry.soshnikov@gmail.com>
 */

'use strict';

/**
 * A regexp-tree plugin to remove unnecessary groups.
 *
 * /(?:a)/ -> /a/
 */

function _toConsumableArray(arr) { if (Array.isArray(arr)) { for (var i = 0, arr2 = Array(arr.length); i < arr.length; i++) { arr2[i] = arr[i]; } return arr2; } else { return Array.from(arr); } }

module.exports = {
  Group: function Group(path) {
    var node = path.node,
        parent = path.parent;

    var childPath = path.getChild();

    if (node.capturing || !childPath) {
      return;
    }

    // Don't optimize \1(?:0) to \10
    if (!hasAppropriateSiblings(path)) {
      return;
    }

    // Don't optimize /a(?:b|c)/ to /ab|c/
    // but /(?:b|c)/ to /b|c/ is ok
    if (childPath.node.type === 'Disjunction' && parent.type !== 'RegExp') {
      return;
    }

    // Don't optimize /(?:ab)+/ to /ab+/
    // but /(?:a)+/ to /a+/ is ok
    // and /(?:[a-d])+/ to /[a-d]+/ is ok too
    if (parent.type === 'Repetition' && childPath.node.type !== 'Char' && childPath.node.type !== 'CharacterClass') {
      return;
    }

    if (childPath.node.type === 'Alternative') {
      var parentPath = path.getParent();
      if (parentPath.node.type === 'Alternative') {
        // /abc(?:def)ghi/ When (?:def) is ungrouped its content must be merged with parent alternative

        parentPath.replace({
          type: 'Alternative',
          expressions: [].concat(_toConsumableArray(parent.expressions.slice(0, path.index)), _toConsumableArray(childPath.node.expressions), _toConsumableArray(parent.expressions.slice(path.index + 1)))
        });
      }
    } else {
      path.replace(childPath.node);
    }
  }
};

function hasAppropriateSiblings(path) {
  var parent = path.parent,
      index = path.index;


  if (parent.type !== 'Alternative') {
    return true;
  }

  var previousNode = parent.expressions[index - 1];
  if (previousNode == null) {
    return true;
  }

  // Don't optimized \1(?:0) to \10
  if (previousNode.type === 'Backreference' && previousNode.kind === 'number') {
    return false;
  }

  // Don't optimized \2(?:0) to \20
  if (previousNode.type === 'Char' && previousNode.kind === 'decimal') {
    return false;
  }

  return true;
}
},{}],45:[function(require,module,exports){
/**
 * LR parser generated by the Syntax tool.
 *
 * https://www.npmjs.com/package/syntax-cli
 *
 *   npm install -g syntax-cli
 *
 *   syntax-cli --help
 *
 * To regenerate run:
 *
 *   syntax-cli \
 *     --grammar ~/path-to-grammar-file \
 *     --mode <parsing-mode> \
 *     --output ~/path-to-output-parser-file.js
 */

'use strict';

/**
 * Matched token text.
 */

var _slicedToArray = function () { function sliceIterator(arr, i) { var _arr = []; var _n = true; var _d = false; var _e = undefined; try { for (var _i = arr[Symbol.iterator](), _s; !(_n = (_s = _i.next()).done); _n = true) { _arr.push(_s.value); if (i && _arr.length === i) break; } } catch (err) { _d = true; _e = err; } finally { try { if (!_n && _i["return"]) _i["return"](); } finally { if (_d) throw _e; } } return _arr; } return function (arr, i) { if (Array.isArray(arr)) { return arr; } else if (Symbol.iterator in Object(arr)) { return sliceIterator(arr, i); } else { throw new TypeError("Invalid attempt to destructure non-iterable instance"); } }; }();

function _toConsumableArray(arr) { if (Array.isArray(arr)) { for (var i = 0, arr2 = Array(arr.length); i < arr.length; i++) { arr2[i] = arr[i]; } return arr2; } else { return Array.from(arr); } }

var yytext = void 0;

/**
 * Length of the matched token text.
 */
var yyleng = void 0;

/**
 * Storage object.
 */
var yy = {};

/**
 * Result of semantic action.
 */
var __ = void 0;

/**
 * Result location object.
 */
var __loc = void 0;

function yyloc(start, end) {
  if (!yy.options.captureLocations) {
    return null;
  }

  // Epsilon doesn't produce location.
  if (!start || !end) {
    return start || end;
  }

  return {
    startOffset: start.startOffset,
    endOffset: end.endOffset,
    startLine: start.startLine,
    endLine: end.endLine,
    startColumn: start.startColumn,
    endColumn: end.endColumn
  };
}

var EOF = '$';

/**
 * List of productions (generated by Syntax tool).
 */
var productions = [[-1, 1, function (_1, _1loc) {
  __loc = yyloc(_1loc, _1loc);__ = _1;
}], [0, 4, function (_1, _2, _3, _4, _1loc, _2loc, _3loc, _4loc) {
  __loc = yyloc(_1loc, _4loc);
  __ = Node({
    type: 'RegExp',
    body: _2,
    flags: checkFlags(_4)
  }, loc(_1loc, _4loc || _3loc));
}], [1, 1, function (_1, _1loc) {
  __loc = yyloc(_1loc, _1loc);__ = _1;
}], [1, 0, function () {
  __loc = null;__ = '';
}], [2, 1, function (_1, _1loc) {
  __loc = yyloc(_1loc, _1loc);__ = _1;
}], [2, 2, function (_1, _2, _1loc, _2loc) {
  __loc = yyloc(_1loc, _2loc);__ = _1 + _2;
}], [3, 1, function (_1, _1loc) {
  __loc = yyloc(_1loc, _1loc);__ = _1;
}], [4, 1, function (_1, _1loc) {
  __loc = yyloc(_1loc, _1loc);__ = _1;
}], [4, 3, function (_1, _2, _3, _1loc, _2loc, _3loc) {
  __loc = yyloc(_1loc, _3loc);
  // Location for empty disjunction: /|/
  var _loc = null;

  if (_2loc) {
    _loc = loc(_1loc || _2loc, _3loc || _2loc);
  };

  __ = Node({
    type: 'Disjunction',
    left: _1,
    right: _3
  }, _loc);
}], [5, 1, function (_1, _1loc) {
  __loc = yyloc(_1loc, _1loc);
  if (_1.length === 0) {
    __ = null;
    return;
  }

  if (_1.length === 1) {
    __ = Node(_1[0], __loc);
  } else {
    __ = Node({
      type: 'Alternative',
      expressions: _1
    }, __loc);
  }
}], [6, 0, function () {
  __loc = null;__ = [];
}], [6, 2, function (_1, _2, _1loc, _2loc) {
  __loc = yyloc(_1loc, _2loc);__ = _1.concat(_2);
}], [7, 1, function (_1, _1loc) {
  __loc = yyloc(_1loc, _1loc);__ = Node(Object.assign({ type: 'Assertion' }, _1), __loc);
}], [7, 2, function (_1, _2, _1loc, _2loc) {
  __loc = yyloc(_1loc, _2loc);
  __ = _1;

  if (_2) {
    __ = Node({
      type: 'Repetition',
      expression: _1,
      quantifier: _2
    }, __loc);
  }
}], [8, 1, function (_1, _1loc) {
  __loc = yyloc(_1loc, _1loc);__ = { kind: '^' };
}], [8, 1, function (_1, _1loc) {
  __loc = yyloc(_1loc, _1loc);__ = { kind: '$' };
}], [8, 1, function (_1, _1loc) {
  __loc = yyloc(_1loc, _1loc);__ = { kind: '\\b' };
}], [8, 1, function (_1, _1loc) {
  __loc = yyloc(_1loc, _1loc);__ = { kind: '\\B' };
}], [8, 3, function (_1, _2, _3, _1loc, _2loc, _3loc) {
  __loc = yyloc(_1loc, _3loc);
  __ = {
    kind: 'Lookahead',
    assertion: _2
  };
}], [8, 3, function (_1, _2, _3, _1loc, _2loc, _3loc) {
  __loc = yyloc(_1loc, _3loc);
  __ = {
    kind: 'Lookahead',
    negative: true,
    assertion: _2
  };
}], [8, 3, function (_1, _2, _3, _1loc, _2loc, _3loc) {
  __loc = yyloc(_1loc, _3loc);
  __ = {
    kind: 'Lookbehind',
    assertion: _2
  };
}], [8, 3, function (_1, _2, _3, _1loc, _2loc, _3loc) {
  __loc = yyloc(_1loc, _3loc);
  __ = {
    kind: 'Lookbehind',
    negative: true,
    assertion: _2
  };
}], [9, 1, function (_1, _1loc) {
  __loc = yyloc(_1loc, _1loc);__ = _1;
}], [9, 1, function (_1, _1loc) {
  __loc = yyloc(_1loc, _1loc);__ = _1;
}], [9, 1, function (_1, _1loc) {
  __loc = yyloc(_1loc, _1loc);__ = _1;
}], [10, 1, function (_1, _1loc) {
  __loc = yyloc(_1loc, _1loc);__ = Char(_1, 'simple', __loc);
}], [10, 1, function (_1, _1loc) {
  __loc = yyloc(_1loc, _1loc);__ = Char(_1.slice(1), 'simple', __loc);__.escaped = true;
}], [10, 1, function (_1, _1loc) {
  __loc = yyloc(_1loc, _1loc);__ = Char(_1, 'unicode', __loc);__.isSurrogatePair = true;
}], [10, 1, function (_1, _1loc) {
  __loc = yyloc(_1loc, _1loc);__ = Char(_1, 'unicode', __loc);
}], [10, 1, function (_1, _1loc) {
  __loc = yyloc(_1loc, _1loc);__ = UnicodeProperty(_1, __loc);
}], [10, 1, function (_1, _1loc) {
  __loc = yyloc(_1loc, _1loc);__ = Char(_1, 'control', __loc);
}], [10, 1, function (_1, _1loc) {
  __loc = yyloc(_1loc, _1loc);__ = Char(_1, 'hex', __loc);
}], [10, 1, function (_1, _1loc) {
  __loc = yyloc(_1loc, _1loc);__ = Char(_1, 'oct', __loc);
}], [10, 1, function (_1, _1loc) {
  __loc = yyloc(_1loc, _1loc);__ = GroupRefOrDecChar(_1, __loc);
}], [10, 1, function (_1, _1loc) {
  __loc = yyloc(_1loc, _1loc);__ = Char(_1, 'meta', __loc);
}], [10, 1, function (_1, _1loc) {
  __loc = yyloc(_1loc, _1loc);__ = Char(_1, 'meta', __loc);
}], [10, 1, function (_1, _1loc) {
  __loc = yyloc(_1loc, _1loc);__ = NamedGroupRefOrChars(_1, _1loc);
}], [11, 1, function (_1, _1loc) {
  __loc = yyloc(_1loc, _1loc);__ = _1;
}], [11, 0], [12, 1, function (_1, _1loc) {
  __loc = yyloc(_1loc, _1loc);__ = _1;
}], [12, 2, function (_1, _2, _1loc, _2loc) {
  __loc = yyloc(_1loc, _2loc);
  _1.greedy = false;
  __ = _1;
}], [13, 1, function (_1, _1loc) {
  __loc = yyloc(_1loc, _1loc);
  __ = Node({
    type: 'Quantifier',
    kind: _1,
    greedy: true
  }, __loc);
}], [13, 1, function (_1, _1loc) {
  __loc = yyloc(_1loc, _1loc);
  __ = Node({
    type: 'Quantifier',
    kind: _1,
    greedy: true
  }, __loc);
}], [13, 1, function (_1, _1loc) {
  __loc = yyloc(_1loc, _1loc);
  __ = Node({
    type: 'Quantifier',
    kind: _1,
    greedy: true
  }, __loc);
}], [13, 1, function (_1, _1loc) {
  __loc = yyloc(_1loc, _1loc);
  var range = getRange(_1);
  __ = Node({
    type: 'Quantifier',
    kind: 'Range',
    from: range[0],
    to: range[0],
    greedy: true
  }, __loc);
}], [13, 1, function (_1, _1loc) {
  __loc = yyloc(_1loc, _1loc);
  __ = Node({
    type: 'Quantifier',
    kind: 'Range',
    from: getRange(_1)[0],
    greedy: true
  }, __loc);
}], [13, 1, function (_1, _1loc) {
  __loc = yyloc(_1loc, _1loc);
  var range = getRange(_1);
  __ = Node({
    type: 'Quantifier',
    kind: 'Range',
    from: range[0],
    to: range[1],
    greedy: true
  }, __loc);
}], [14, 1, function (_1, _1loc) {
  __loc = yyloc(_1loc, _1loc);__ = _1;
}], [14, 1, function (_1, _1loc) {
  __loc = yyloc(_1loc, _1loc);__ = _1;
}], [15, 3, function (_1, _2, _3, _1loc, _2loc, _3loc) {
  __loc = yyloc(_1loc, _3loc);
  var nameRaw = String(_1);
  var name = decodeUnicodeGroupName(nameRaw);
  if (!yy.options.allowGroupNameDuplicates && namedGroups.hasOwnProperty(name)) {
    throw new SyntaxError('Duplicate of the named group "' + name + '".');
  }

  namedGroups[name] = _1.groupNumber;

  __ = Node({
    type: 'Group',
    capturing: true,
    name: name,
    nameRaw: nameRaw,
    number: _1.groupNumber,
    expression: _2
  }, __loc);
}], [15, 3, function (_1, _2, _3, _1loc, _2loc, _3loc) {
  __loc = yyloc(_1loc, _3loc);
  __ = Node({
    type: 'Group',
    capturing: true,
    number: _1.groupNumber,
    expression: _2
  }, __loc);
}], [16, 3, function (_1, _2, _3, _1loc, _2loc, _3loc) {
  __loc = yyloc(_1loc, _3loc);
  __ = Node({
    type: 'Group',
    capturing: false,
    expression: _2
  }, __loc);
}], [17, 3, function (_1, _2, _3, _1loc, _2loc, _3loc) {
  __loc = yyloc(_1loc, _3loc);
  __ = Node({
    type: 'CharacterClass',
    negative: true,
    expressions: _2
  }, __loc);
}], [17, 3, function (_1, _2, _3, _1loc, _2loc, _3loc) {
  __loc = yyloc(_1loc, _3loc);
  __ = Node({
    type: 'CharacterClass',
    expressions: _2
  }, __loc);
}], [18, 0, function () {
  __loc = null;__ = [];
}], [18, 1, function (_1, _1loc) {
  __loc = yyloc(_1loc, _1loc);__ = _1;
}], [19, 1, function (_1, _1loc) {
  __loc = yyloc(_1loc, _1loc);__ = [_1];
}], [19, 2, function (_1, _2, _1loc, _2loc) {
  __loc = yyloc(_1loc, _2loc);__ = [_1].concat(_2);
}], [19, 4, function (_1, _2, _3, _4, _1loc, _2loc, _3loc, _4loc) {
  __loc = yyloc(_1loc, _4loc);
  checkClassRange(_1, _3);

  __ = [Node({
    type: 'ClassRange',
    from: _1,
    to: _3
  }, loc(_1loc, _3loc))];

  if (_4) {
    __ = __.concat(_4);
  }
}], [20, 1, function (_1, _1loc) {
  __loc = yyloc(_1loc, _1loc);__ = _1;
}], [20, 2, function (_1, _2, _1loc, _2loc) {
  __loc = yyloc(_1loc, _2loc);__ = [_1].concat(_2);
}], [20, 4, function (_1, _2, _3, _4, _1loc, _2loc, _3loc, _4loc) {
  __loc = yyloc(_1loc, _4loc);
  checkClassRange(_1, _3);

  __ = [Node({
    type: 'ClassRange',
    from: _1,
    to: _3
  }, loc(_1loc, _3loc))];

  if (_4) {
    __ = __.concat(_4);
  }
}], [21, 1, function (_1, _1loc) {
  __loc = yyloc(_1loc, _1loc);__ = Char(_1, 'simple', __loc);
}], [21, 1, function (_1, _1loc) {
  __loc = yyloc(_1loc, _1loc);__ = _1;
}], [22, 1, function (_1, _1loc) {
  __loc = yyloc(_1loc, _1loc);__ = _1;
}], [22, 1, function (_1, _1loc) {
  __loc = yyloc(_1loc, _1loc);__ = Char(_1, 'meta', __loc);
}]];

/**
 * Encoded tokens map.
 */
var tokens = { "SLASH": "23", "CHAR": "24", "BAR": "25", "BOS": "26", "EOS": "27", "ESC_b": "28", "ESC_B": "29", "POS_LA_ASSERT": "30", "R_PAREN": "31", "NEG_LA_ASSERT": "32", "POS_LB_ASSERT": "33", "NEG_LB_ASSERT": "34", "ESC_CHAR": "35", "U_CODE_SURROGATE": "36", "U_CODE": "37", "U_PROP_VALUE_EXP": "38", "CTRL_CH": "39", "HEX_CODE": "40", "OCT_CODE": "41", "DEC_CODE": "42", "META_CHAR": "43", "ANY": "44", "NAMED_GROUP_REF": "45", "Q_MARK": "46", "STAR": "47", "PLUS": "48", "RANGE_EXACT": "49", "RANGE_OPEN": "50", "RANGE_CLOSED": "51", "NAMED_CAPTURE_GROUP": "52", "L_PAREN": "53", "NON_CAPTURE_GROUP": "54", "NEG_CLASS": "55", "R_BRACKET": "56", "L_BRACKET": "57", "DASH": "58", "$": "59" };

/**
 * Parsing table (generated by Syntax tool).
 */
var table = [{ "0": 1, "23": "s2" }, { "59": "acc" }, { "3": 3, "4": 4, "5": 5, "6": 6, "23": "r10", "24": "r10", "25": "r10", "26": "r10", "27": "r10", "28": "r10", "29": "r10", "30": "r10", "32": "r10", "33": "r10", "34": "r10", "35": "r10", "36": "r10", "37": "r10", "38": "r10", "39": "r10", "40": "r10", "41": "r10", "42": "r10", "43": "r10", "44": "r10", "45": "r10", "52": "r10", "53": "r10", "54": "r10", "55": "r10", "57": "r10" }, { "23": "s7" }, { "23": "r6", "25": "s12" }, { "23": "r7", "25": "r7", "31": "r7" }, { "7": 14, "8": 15, "9": 16, "10": 25, "14": 27, "15": 42, "16": 43, "17": 26, "23": "r9", "24": "s28", "25": "r9", "26": "s17", "27": "s18", "28": "s19", "29": "s20", "30": "s21", "31": "r9", "32": "s22", "33": "s23", "34": "s24", "35": "s29", "36": "s30", "37": "s31", "38": "s32", "39": "s33", "40": "s34", "41": "s35", "42": "s36", "43": "s37", "44": "s38", "45": "s39", "52": "s44", "53": "s45", "54": "s46", "55": "s40", "57": "s41" }, { "1": 8, "2": 9, "24": "s10", "59": "r3" }, { "59": "r1" }, { "24": "s11", "59": "r2" }, { "24": "r4", "59": "r4" }, { "24": "r5", "59": "r5" }, { "5": 13, "6": 6, "23": "r10", "24": "r10", "25": "r10", "26": "r10", "27": "r10", "28": "r10", "29": "r10", "30": "r10", "31": "r10", "32": "r10", "33": "r10", "34": "r10", "35": "r10", "36": "r10", "37": "r10", "38": "r10", "39": "r10", "40": "r10", "41": "r10", "42": "r10", "43": "r10", "44": "r10", "45": "r10", "52": "r10", "53": "r10", "54": "r10", "55": "r10", "57": "r10" }, { "23": "r8", "25": "r8", "31": "r8" }, { "23": "r11", "24": "r11", "25": "r11", "26": "r11", "27": "r11", "28": "r11", "29": "r11", "30": "r11", "31": "r11", "32": "r11", "33": "r11", "34": "r11", "35": "r11", "36": "r11", "37": "r11", "38": "r11", "39": "r11", "40": "r11", "41": "r11", "42": "r11", "43": "r11", "44": "r11", "45": "r11", "52": "r11", "53": "r11", "54": "r11", "55": "r11", "57": "r11" }, { "23": "r12", "24": "r12", "25": "r12", "26": "r12", "27": "r12", "28": "r12", "29": "r12", "30": "r12", "31": "r12", "32": "r12", "33": "r12", "34": "r12", "35": "r12", "36": "r12", "37": "r12", "38": "r12", "39": "r12", "40": "r12", "41": "r12", "42": "r12", "43": "r12", "44": "r12", "45": "r12", "52": "r12", "53": "r12", "54": "r12", "55": "r12", "57": "r12" }, { "11": 47, "12": 48, "13": 49, "23": "r38", "24": "r38", "25": "r38", "26": "r38", "27": "r38", "28": "r38", "29": "r38", "30": "r38", "31": "r38", "32": "r38", "33": "r38", "34": "r38", "35": "r38", "36": "r38", "37": "r38", "38": "r38", "39": "r38", "40": "r38", "41": "r38", "42": "r38", "43": "r38", "44": "r38", "45": "r38", "46": "s52", "47": "s50", "48": "s51", "49": "s53", "50": "s54", "51": "s55", "52": "r38", "53": "r38", "54": "r38", "55": "r38", "57": "r38" }, { "23": "r14", "24": "r14", "25": "r14", "26": "r14", "27": "r14", "28": "r14", "29": "r14", "30": "r14", "31": "r14", "32": "r14", "33": "r14", "34": "r14", "35": "r14", "36": "r14", "37": "r14", "38": "r14", "39": "r14", "40": "r14", "41": "r14", "42": "r14", "43": "r14", "44": "r14", "45": "r14", "52": "r14", "53": "r14", "54": "r14", "55": "r14", "57": "r14" }, { "23": "r15", "24": "r15", "25": "r15", "26": "r15", "27": "r15", "28": "r15", "29": "r15", "30": "r15", "31": "r15", "32": "r15", "33": "r15", "34": "r15", "35": "r15", "36": "r15", "37": "r15", "38": "r15", "39": "r15", "40": "r15", "41": "r15", "42": "r15", "43": "r15", "44": "r15", "45": "r15", "52": "r15", "53": "r15", "54": "r15", "55": "r15", "57": "r15" }, { "23": "r16", "24": "r16", "25": "r16", "26": "r16", "27": "r16", "28": "r16", "29": "r16", "30": "r16", "31": "r16", "32": "r16", "33": "r16", "34": "r16", "35": "r16", "36": "r16", "37": "r16", "38": "r16", "39": "r16", "40": "r16", "41": "r16", "42": "r16", "43": "r16", "44": "r16", "45": "r16", "52": "r16", "53": "r16", "54": "r16", "55": "r16", "57": "r16" }, { "23": "r17", "24": "r17", "25": "r17", "26": "r17", "27": "r17", "28": "r17", "29": "r17", "30": "r17", "31": "r17", "32": "r17", "33": "r17", "34": "r17", "35": "r17", "36": "r17", "37": "r17", "38": "r17", "39": "r17", "40": "r17", "41": "r17", "42": "r17", "43": "r17", "44": "r17", "45": "r17", "52": "r17", "53": "r17", "54": "r17", "55": "r17", "57": "r17" }, { "4": 57, "5": 5, "6": 6, "24": "r10", "25": "r10", "26": "r10", "27": "r10", "28": "r10", "29": "r10", "30": "r10", "31": "r10", "32": "r10", "33": "r10", "34": "r10", "35": "r10", "36": "r10", "37": "r10", "38": "r10", "39": "r10", "40": "r10", "41": "r10", "42": "r10", "43": "r10", "44": "r10", "45": "r10", "52": "r10", "53": "r10", "54": "r10", "55": "r10", "57": "r10" }, { "4": 59, "5": 5, "6": 6, "24": "r10", "25": "r10", "26": "r10", "27": "r10", "28": "r10", "29": "r10", "30": "r10", "31": "r10", "32": "r10", "33": "r10", "34": "r10", "35": "r10", "36": "r10", "37": "r10", "38": "r10", "39": "r10", "40": "r10", "41": "r10", "42": "r10", "43": "r10", "44": "r10", "45": "r10", "52": "r10", "53": "r10", "54": "r10", "55": "r10", "57": "r10" }, { "4": 61, "5": 5, "6": 6, "24": "r10", "25": "r10", "26": "r10", "27": "r10", "28": "r10", "29": "r10", "30": "r10", "31": "r10", "32": "r10", "33": "r10", "34": "r10", "35": "r10", "36": "r10", "37": "r10", "38": "r10", "39": "r10", "40": "r10", "41": "r10", "42": "r10", "43": "r10", "44": "r10", "45": "r10", "52": "r10", "53": "r10", "54": "r10", "55": "r10", "57": "r10" }, { "4": 63, "5": 5, "6": 6, "24": "r10", "25": "r10", "26": "r10", "27": "r10", "28": "r10", "29": "r10", "30": "r10", "31": "r10", "32": "r10", "33": "r10", "34": "r10", "35": "r10", "36": "r10", "37": "r10", "38": "r10", "39": "r10", "40": "r10", "41": "r10", "42": "r10", "43": "r10", "44": "r10", "45": "r10", "52": "r10", "53": "r10", "54": "r10", "55": "r10", "57": "r10" }, { "23": "r22", "24": "r22", "25": "r22", "26": "r22", "27": "r22", "28": "r22", "29": "r22", "30": "r22", "31": "r22", "32": "r22", "33": "r22", "34": "r22", "35": "r22", "36": "r22", "37": "r22", "38": "r22", "39": "r22", "40": "r22", "41": "r22", "42": "r22", "43": "r22", "44": "r22", "45": "r22", "46": "r22", "47": "r22", "48": "r22", "49": "r22", "50": "r22", "51": "r22", "52": "r22", "53": "r22", "54": "r22", "55": "r22", "57": "r22" }, { "23": "r23", "24": "r23", "25": "r23", "26": "r23", "27": "r23", "28": "r23", "29": "r23", "30": "r23", "31": "r23", "32": "r23", "33": "r23", "34": "r23", "35": "r23", "36": "r23", "37": "r23", "38": "r23", "39": "r23", "40": "r23", "41": "r23", "42": "r23", "43": "r23", "44": "r23", "45": "r23", "46": "r23", "47": "r23", "48": "r23", "49": "r23", "50": "r23", "51": "r23", "52": "r23", "53": "r23", "54": "r23", "55": "r23", "57": "r23" }, { "23": "r24", "24": "r24", "25": "r24", "26": "r24", "27": "r24", "28": "r24", "29": "r24", "30": "r24", "31": "r24", "32": "r24", "33": "r24", "34": "r24", "35": "r24", "36": "r24", "37": "r24", "38": "r24", "39": "r24", "40": "r24", "41": "r24", "42": "r24", "43": "r24", "44": "r24", "45": "r24", "46": "r24", "47": "r24", "48": "r24", "49": "r24", "50": "r24", "51": "r24", "52": "r24", "53": "r24", "54": "r24", "55": "r24", "57": "r24" }, { "23": "r25", "24": "r25", "25": "r25", "26": "r25", "27": "r25", "28": "r25", "29": "r25", "30": "r25", "31": "r25", "32": "r25", "33": "r25", "34": "r25", "35": "r25", "36": "r25", "37": "r25", "38": "r25", "39": "r25", "40": "r25", "41": "r25", "42": "r25", "43": "r25", "44": "r25", "45": "r25", "46": "r25", "47": "r25", "48": "r25", "49": "r25", "50": "r25", "51": "r25", "52": "r25", "53": "r25", "54": "r25", "55": "r25", "56": "r25", "57": "r25", "58": "r25" }, { "23": "r26", "24": "r26", "25": "r26", "26": "r26", "27": "r26", "28": "r26", "29": "r26", "30": "r26", "31": "r26", "32": "r26", "33": "r26", "34": "r26", "35": "r26", "36": "r26", "37": "r26", "38": "r26", "39": "r26", "40": "r26", "41": "r26", "42": "r26", "43": "r26", "44": "r26", "45": "r26", "46": "r26", "47": "r26", "48": "r26", "49": "r26", "50": "r26", "51": "r26", "52": "r26", "53": "r26", "54": "r26", "55": "r26", "56": "r26", "57": "r26", "58": "r26" }, { "23": "r27", "24": "r27", "25": "r27", "26": "r27", "27": "r27", "28": "r27", "29": "r27", "30": "r27", "31": "r27", "32": "r27", "33": "r27", "34": "r27", "35": "r27", "36": "r27", "37": "r27", "38": "r27", "39": "r27", "40": "r27", "41": "r27", "42": "r27", "43": "r27", "44": "r27", "45": "r27", "46": "r27", "47": "r27", "48": "r27", "49": "r27", "50": "r27", "51": "r27", "52": "r27", "53": "r27", "54": "r27", "55": "r27", "56": "r27", "57": "r27", "58": "r27" }, { "23": "r28", "24": "r28", "25": "r28", "26": "r28", "27": "r28", "28": "r28", "29": "r28", "30": "r28", "31": "r28", "32": "r28", "33": "r28", "34": "r28", "35": "r28", "36": "r28", "37": "r28", "38": "r28", "39": "r28", "40": "r28", "41": "r28", "42": "r28", "43": "r28", "44": "r28", "45": "r28", "46": "r28", "47": "r28", "48": "r28", "49": "r28", "50": "r28", "51": "r28", "52": "r28", "53": "r28", "54": "r28", "55": "r28", "56": "r28", "57": "r28", "58": "r28" }, { "23": "r29", "24": "r29", "25": "r29", "26": "r29", "27": "r29", "28": "r29", "29": "r29", "30": "r29", "31": "r29", "32": "r29", "33": "r29", "34": "r29", "35": "r29", "36": "r29", "37": "r29", "38": "r29", "39": "r29", "40": "r29", "41": "r29", "42": "r29", "43": "r29", "44": "r29", "45": "r29", "46": "r29", "47": "r29", "48": "r29", "49": "r29", "50": "r29", "51": "r29", "52": "r29", "53": "r29", "54": "r29", "55": "r29", "56": "r29", "57": "r29", "58": "r29" }, { "23": "r30", "24": "r30", "25": "r30", "26": "r30", "27": "r30", "28": "r30", "29": "r30", "30": "r30", "31": "r30", "32": "r30", "33": "r30", "34": "r30", "35": "r30", "36": "r30", "37": "r30", "38": "r30", "39": "r30", "40": "r30", "41": "r30", "42": "r30", "43": "r30", "44": "r30", "45": "r30", "46": "r30", "47": "r30", "48": "r30", "49": "r30", "50": "r30", "51": "r30", "52": "r30", "53": "r30", "54": "r30", "55": "r30", "56": "r30", "57": "r30", "58": "r30" }, { "23": "r31", "24": "r31", "25": "r31", "26": "r31", "27": "r31", "28": "r31", "29": "r31", "30": "r31", "31": "r31", "32": "r31", "33": "r31", "34": "r31", "35": "r31", "36": "r31", "37": "r31", "38": "r31", "39": "r31", "40": "r31", "41": "r31", "42": "r31", "43": "r31", "44": "r31", "45": "r31", "46": "r31", "47": "r31", "48": "r31", "49": "r31", "50": "r31", "51": "r31", "52": "r31", "53": "r31", "54": "r31", "55": "r31", "56": "r31", "57": "r31", "58": "r31" }, { "23": "r32", "24": "r32", "25": "r32", "26": "r32", "27": "r32", "28": "r32", "29": "r32", "30": "r32", "31": "r32", "32": "r32", "33": "r32", "34": "r32", "35": "r32", "36": "r32", "37": "r32", "38": "r32", "39": "r32", "40": "r32", "41": "r32", "42": "r32", "43": "r32", "44": "r32", "45": "r32", "46": "r32", "47": "r32", "48": "r32", "49": "r32", "50": "r32", "51": "r32", "52": "r32", "53": "r32", "54": "r32", "55": "r32", "56": "r32", "57": "r32", "58": "r32" }, { "23": "r33", "24": "r33", "25": "r33", "26": "r33", "27": "r33", "28": "r33", "29": "r33", "30": "r33", "31": "r33", "32": "r33", "33": "r33", "34": "r33", "35": "r33", "36": "r33", "37": "r33", "38": "r33", "39": "r33", "40": "r33", "41": "r33", "42": "r33", "43": "r33", "44": "r33", "45": "r33", "46": "r33", "47": "r33", "48": "r33", "49": "r33", "50": "r33", "51": "r33", "52": "r33", "53": "r33", "54": "r33", "55": "r33", "56": "r33", "57": "r33", "58": "r33" }, { "23": "r34", "24": "r34", "25": "r34", "26": "r34", "27": "r34", "28": "r34", "29": "r34", "30": "r34", "31": "r34", "32": "r34", "33": "r34", "34": "r34", "35": "r34", "36": "r34", "37": "r34", "38": "r34", "39": "r34", "40": "r34", "41": "r34", "42": "r34", "43": "r34", "44": "r34", "45": "r34", "46": "r34", "47": "r34", "48": "r34", "49": "r34", "50": "r34", "51": "r34", "52": "r34", "53": "r34", "54": "r34", "55": "r34", "56": "r34", "57": "r34", "58": "r34" }, { "23": "r35", "24": "r35", "25": "r35", "26": "r35", "27": "r35", "28": "r35", "29": "r35", "30": "r35", "31": "r35", "32": "r35", "33": "r35", "34": "r35", "35": "r35", "36": "r35", "37": "r35", "38": "r35", "39": "r35", "40": "r35", "41": "r35", "42": "r35", "43": "r35", "44": "r35", "45": "r35", "46": "r35", "47": "r35", "48": "r35", "49": "r35", "50": "r35", "51": "r35", "52": "r35", "53": "r35", "54": "r35", "55": "r35", "56": "r35", "57": "r35", "58": "r35" }, { "23": "r36", "24": "r36", "25": "r36", "26": "r36", "27": "r36", "28": "r36", "29": "r36", "30": "r36", "31": "r36", "32": "r36", "33": "r36", "34": "r36", "35": "r36", "36": "r36", "37": "r36", "38": "r36", "39": "r36", "40": "r36", "41": "r36", "42": "r36", "43": "r36", "44": "r36", "45": "r36", "46": "r36", "47": "r36", "48": "r36", "49": "r36", "50": "r36", "51": "r36", "52": "r36", "53": "r36", "54": "r36", "55": "r36", "56": "r36", "57": "r36", "58": "r36" }, { "10": 70, "18": 65, "19": 66, "21": 67, "22": 69, "24": "s28", "28": "s71", "35": "s29", "36": "s30", "37": "s31", "38": "s32", "39": "s33", "40": "s34", "41": "s35", "42": "s36", "43": "s37", "44": "s38", "45": "s39", "56": "r54", "58": "s68" }, { "10": 70, "18": 83, "19": 66, "21": 67, "22": 69, "24": "s28", "28": "s71", "35": "s29", "36": "s30", "37": "s31", "38": "s32", "39": "s33", "40": "s34", "41": "s35", "42": "s36", "43": "s37", "44": "s38", "45": "s39", "56": "r54", "58": "s68" }, { "23": "r47", "24": "r47", "25": "r47", "26": "r47", "27": "r47", "28": "r47", "29": "r47", "30": "r47", "31": "r47", "32": "r47", "33": "r47", "34": "r47", "35": "r47", "36": "r47", "37": "r47", "38": "r47", "39": "r47", "40": "r47", "41": "r47", "42": "r47", "43": "r47", "44": "r47", "45": "r47", "46": "r47", "47": "r47", "48": "r47", "49": "r47", "50": "r47", "51": "r47", "52": "r47", "53": "r47", "54": "r47", "55": "r47", "57": "r47" }, { "23": "r48", "24": "r48", "25": "r48", "26": "r48", "27": "r48", "28": "r48", "29": "r48", "30": "r48", "31": "r48", "32": "r48", "33": "r48", "34": "r48", "35": "r48", "36": "r48", "37": "r48", "38": "r48", "39": "r48", "40": "r48", "41": "r48", "42": "r48", "43": "r48", "44": "r48", "45": "r48", "46": "r48", "47": "r48", "48": "r48", "49": "r48", "50": "r48", "51": "r48", "52": "r48", "53": "r48", "54": "r48", "55": "r48", "57": "r48" }, { "4": 85, "5": 5, "6": 6, "24": "r10", "25": "r10", "26": "r10", "27": "r10", "28": "r10", "29": "r10", "30": "r10", "31": "r10", "32": "r10", "33": "r10", "34": "r10", "35": "r10", "36": "r10", "37": "r10", "38": "r10", "39": "r10", "40": "r10", "41": "r10", "42": "r10", "43": "r10", "44": "r10", "45": "r10", "52": "r10", "53": "r10", "54": "r10", "55": "r10", "57": "r10" }, { "4": 87, "5": 5, "6": 6, "24": "r10", "25": "r10", "26": "r10", "27": "r10", "28": "r10", "29": "r10", "30": "r10", "31": "r10", "32": "r10", "33": "r10", "34": "r10", "35": "r10", "36": "r10", "37": "r10", "38": "r10", "39": "r10", "40": "r10", "41": "r10", "42": "r10", "43": "r10", "44": "r10", "45": "r10", "52": "r10", "53": "r10", "54": "r10", "55": "r10", "57": "r10" }, { "4": 89, "5": 5, "6": 6, "24": "r10", "25": "r10", "26": "r10", "27": "r10", "28": "r10", "29": "r10", "30": "r10", "31": "r10", "32": "r10", "33": "r10", "34": "r10", "35": "r10", "36": "r10", "37": "r10", "38": "r10", "39": "r10", "40": "r10", "41": "r10", "42": "r10", "43": "r10", "44": "r10", "45": "r10", "52": "r10", "53": "r10", "54": "r10", "55": "r10", "57": "r10" }, { "23": "r13", "24": "r13", "25": "r13", "26": "r13", "27": "r13", "28": "r13", "29": "r13", "30": "r13", "31": "r13", "32": "r13", "33": "r13", "34": "r13", "35": "r13", "36": "r13", "37": "r13", "38": "r13", "39": "r13", "40": "r13", "41": "r13", "42": "r13", "43": "r13", "44": "r13", "45": "r13", "52": "r13", "53": "r13", "54": "r13", "55": "r13", "57": "r13" }, { "23": "r37", "24": "r37", "25": "r37", "26": "r37", "27": "r37", "28": "r37", "29": "r37", "30": "r37", "31": "r37", "32": "r37", "33": "r37", "34": "r37", "35": "r37", "36": "r37", "37": "r37", "38": "r37", "39": "r37", "40": "r37", "41": "r37", "42": "r37", "43": "r37", "44": "r37", "45": "r37", "52": "r37", "53": "r37", "54": "r37", "55": "r37", "57": "r37" }, { "23": "r39", "24": "r39", "25": "r39", "26": "r39", "27": "r39", "28": "r39", "29": "r39", "30": "r39", "31": "r39", "32": "r39", "33": "r39", "34": "r39", "35": "r39", "36": "r39", "37": "r39", "38": "r39", "39": "r39", "40": "r39", "41": "r39", "42": "r39", "43": "r39", "44": "r39", "45": "r39", "46": "s56", "52": "r39", "53": "r39", "54": "r39", "55": "r39", "57": "r39" }, { "23": "r41", "24": "r41", "25": "r41", "26": "r41", "27": "r41", "28": "r41", "29": "r41", "30": "r41", "31": "r41", "32": "r41", "33": "r41", "34": "r41", "35": "r41", "36": "r41", "37": "r41", "38": "r41", "39": "r41", "40": "r41", "41": "r41", "42": "r41", "43": "r41", "44": "r41", "45": "r41", "46": "r41", "52": "r41", "53": "r41", "54": "r41", "55": "r41", "57": "r41" }, { "23": "r42", "24": "r42", "25": "r42", "26": "r42", "27": "r42", "28": "r42", "29": "r42", "30": "r42", "31": "r42", "32": "r42", "33": "r42", "34": "r42", "35": "r42", "36": "r42", "37": "r42", "38": "r42", "39": "r42", "40": "r42", "41": "r42", "42": "r42", "43": "r42", "44": "r42", "45": "r42", "46": "r42", "52": "r42", "53": "r42", "54": "r42", "55": "r42", "57": "r42" }, { "23": "r43", "24": "r43", "25": "r43", "26": "r43", "27": "r43", "28": "r43", "29": "r43", "30": "r43", "31": "r43", "32": "r43", "33": "r43", "34": "r43", "35": "r43", "36": "r43", "37": "r43", "38": "r43", "39": "r43", "40": "r43", "41": "r43", "42": "r43", "43": "r43", "44": "r43", "45": "r43", "46": "r43", "52": "r43", "53": "r43", "54": "r43", "55": "r43", "57": "r43" }, { "23": "r44", "24": "r44", "25": "r44", "26": "r44", "27": "r44", "28": "r44", "29": "r44", "30": "r44", "31": "r44", "32": "r44", "33": "r44", "34": "r44", "35": "r44", "36": "r44", "37": "r44", "38": "r44", "39": "r44", "40": "r44", "41": "r44", "42": "r44", "43": "r44", "44": "r44", "45": "r44", "46": "r44", "52": "r44", "53": "r44", "54": "r44", "55": "r44", "57": "r44" }, { "23": "r45", "24": "r45", "25": "r45", "26": "r45", "27": "r45", "28": "r45", "29": "r45", "30": "r45", "31": "r45", "32": "r45", "33": "r45", "34": "r45", "35": "r45", "36": "r45", "37": "r45", "38": "r45", "39": "r45", "40": "r45", "41": "r45", "42": "r45", "43": "r45", "44": "r45", "45": "r45", "46": "r45", "52": "r45", "53": "r45", "54": "r45", "55": "r45", "57": "r45" }, { "23": "r46", "24": "r46", "25": "r46", "26": "r46", "27": "r46", "28": "r46", "29": "r46", "30": "r46", "31": "r46", "32": "r46", "33": "r46", "34": "r46", "35": "r46", "36": "r46", "37": "r46", "38": "r46", "39": "r46", "40": "r46", "41": "r46", "42": "r46", "43": "r46", "44": "r46", "45": "r46", "46": "r46", "52": "r46", "53": "r46", "54": "r46", "55": "r46", "57": "r46" }, { "23": "r40", "24": "r40", "25": "r40", "26": "r40", "27": "r40", "28": "r40", "29": "r40", "30": "r40", "31": "r40", "32": "r40", "33": "r40", "34": "r40", "35": "r40", "36": "r40", "37": "r40", "38": "r40", "39": "r40", "40": "r40", "41": "r40", "42": "r40", "43": "r40", "44": "r40", "45": "r40", "52": "r40", "53": "r40", "54": "r40", "55": "r40", "57": "r40" }, { "25": "s12", "31": "s58" }, { "23": "r18", "24": "r18", "25": "r18", "26": "r18", "27": "r18", "28": "r18", "29": "r18", "30": "r18", "31": "r18", "32": "r18", "33": "r18", "34": "r18", "35": "r18", "36": "r18", "37": "r18", "38": "r18", "39": "r18", "40": "r18", "41": "r18", "42": "r18", "43": "r18", "44": "r18", "45": "r18", "52": "r18", "53": "r18", "54": "r18", "55": "r18", "57": "r18" }, { "25": "s12", "31": "s60" }, { "23": "r19", "24": "r19", "25": "r19", "26": "r19", "27": "r19", "28": "r19", "29": "r19", "30": "r19", "31": "r19", "32": "r19", "33": "r19", "34": "r19", "35": "r19", "36": "r19", "37": "r19", "38": "r19", "39": "r19", "40": "r19", "41": "r19", "42": "r19", "43": "r19", "44": "r19", "45": "r19", "52": "r19", "53": "r19", "54": "r19", "55": "r19", "57": "r19" }, { "25": "s12", "31": "s62" }, { "23": "r20", "24": "r20", "25": "r20", "26": "r20", "27": "r20", "28": "r20", "29": "r20", "30": "r20", "31": "r20", "32": "r20", "33": "r20", "34": "r20", "35": "r20", "36": "r20", "37": "r20", "38": "r20", "39": "r20", "40": "r20", "41": "r20", "42": "r20", "43": "r20", "44": "r20", "45": "r20", "52": "r20", "53": "r20", "54": "r20", "55": "r20", "57": "r20" }, { "25": "s12", "31": "s64" }, { "23": "r21", "24": "r21", "25": "r21", "26": "r21", "27": "r21", "28": "r21", "29": "r21", "30": "r21", "31": "r21", "32": "r21", "33": "r21", "34": "r21", "35": "r21", "36": "r21", "37": "r21", "38": "r21", "39": "r21", "40": "r21", "41": "r21", "42": "r21", "43": "r21", "44": "r21", "45": "r21", "52": "r21", "53": "r21", "54": "r21", "55": "r21", "57": "r21" }, { "56": "s72" }, { "56": "r55" }, { "10": 70, "20": 73, "21": 75, "22": 76, "24": "s28", "28": "s71", "35": "s29", "36": "s30", "37": "s31", "38": "s32", "39": "s33", "40": "s34", "41": "s35", "42": "s36", "43": "s37", "44": "s38", "45": "s39", "56": "r56", "58": "s74" }, { "24": "r62", "28": "r62", "35": "r62", "36": "r62", "37": "r62", "38": "r62", "39": "r62", "40": "r62", "41": "r62", "42": "r62", "43": "r62", "44": "r62", "45": "r62", "56": "r62", "58": "r62" }, { "24": "r63", "28": "r63", "35": "r63", "36": "r63", "37": "r63", "38": "r63", "39": "r63", "40": "r63", "41": "r63", "42": "r63", "43": "r63", "44": "r63", "45": "r63", "56": "r63", "58": "r63" }, { "24": "r64", "28": "r64", "35": "r64", "36": "r64", "37": "r64", "38": "r64", "39": "r64", "40": "r64", "41": "r64", "42": "r64", "43": "r64", "44": "r64", "45": "r64", "56": "r64", "58": "r64" }, { "24": "r65", "28": "r65", "35": "r65", "36": "r65", "37": "r65", "38": "r65", "39": "r65", "40": "r65", "41": "r65", "42": "r65", "43": "r65", "44": "r65", "45": "r65", "56": "r65", "58": "r65" }, { "23": "r52", "24": "r52", "25": "r52", "26": "r52", "27": "r52", "28": "r52", "29": "r52", "30": "r52", "31": "r52", "32": "r52", "33": "r52", "34": "r52", "35": "r52", "36": "r52", "37": "r52", "38": "r52", "39": "r52", "40": "r52", "41": "r52", "42": "r52", "43": "r52", "44": "r52", "45": "r52", "46": "r52", "47": "r52", "48": "r52", "49": "r52", "50": "r52", "51": "r52", "52": "r52", "53": "r52", "54": "r52", "55": "r52", "57": "r52" }, { "56": "r57" }, { "10": 70, "21": 77, "22": 69, "24": "s28", "28": "s71", "35": "s29", "36": "s30", "37": "s31", "38": "s32", "39": "s33", "40": "s34", "41": "s35", "42": "s36", "43": "s37", "44": "s38", "45": "s39", "56": "r62", "58": "s68" }, { "56": "r59" }, { "10": 70, "20": 79, "21": 75, "22": 76, "24": "s28", "28": "s71", "35": "s29", "36": "s30", "37": "s31", "38": "s32", "39": "s33", "40": "s34", "41": "s35", "42": "s36", "43": "s37", "44": "s38", "45": "s39", "56": "r63", "58": "s80" }, { "10": 70, "18": 78, "19": 66, "21": 67, "22": 69, "24": "s28", "28": "s71", "35": "s29", "36": "s30", "37": "s31", "38": "s32", "39": "s33", "40": "s34", "41": "s35", "42": "s36", "43": "s37", "44": "s38", "45": "s39", "56": "r54", "58": "s68" }, { "56": "r58" }, { "56": "r60" }, { "10": 70, "21": 81, "22": 69, "24": "s28", "28": "s71", "35": "s29", "36": "s30", "37": "s31", "38": "s32", "39": "s33", "40": "s34", "41": "s35", "42": "s36", "43": "s37", "44": "s38", "45": "s39", "56": "r62", "58": "s68" }, { "10": 70, "18": 82, "19": 66, "21": 67, "22": 69, "24": "s28", "28": "s71", "35": "s29", "36": "s30", "37": "s31", "38": "s32", "39": "s33", "40": "s34", "41": "s35", "42": "s36", "43": "s37", "44": "s38", "45": "s39", "56": "r54", "58": "s68" }, { "56": "r61" }, { "56": "s84" }, { "23": "r53", "24": "r53", "25": "r53", "26": "r53", "27": "r53", "28": "r53", "29": "r53", "30": "r53", "31": "r53", "32": "r53", "33": "r53", "34": "r53", "35": "r53", "36": "r53", "37": "r53", "38": "r53", "39": "r53", "40": "r53", "41": "r53", "42": "r53", "43": "r53", "44": "r53", "45": "r53", "46": "r53", "47": "r53", "48": "r53", "49": "r53", "50": "r53", "51": "r53", "52": "r53", "53": "r53", "54": "r53", "55": "r53", "57": "r53" }, { "25": "s12", "31": "s86" }, { "23": "r49", "24": "r49", "25": "r49", "26": "r49", "27": "r49", "28": "r49", "29": "r49", "30": "r49", "31": "r49", "32": "r49", "33": "r49", "34": "r49", "35": "r49", "36": "r49", "37": "r49", "38": "r49", "39": "r49", "40": "r49", "41": "r49", "42": "r49", "43": "r49", "44": "r49", "45": "r49", "46": "r49", "47": "r49", "48": "r49", "49": "r49", "50": "r49", "51": "r49", "52": "r49", "53": "r49", "54": "r49", "55": "r49", "57": "r49" }, { "25": "s12", "31": "s88" }, { "23": "r50", "24": "r50", "25": "r50", "26": "r50", "27": "r50", "28": "r50", "29": "r50", "30": "r50", "31": "r50", "32": "r50", "33": "r50", "34": "r50", "35": "r50", "36": "r50", "37": "r50", "38": "r50", "39": "r50", "40": "r50", "41": "r50", "42": "r50", "43": "r50", "44": "r50", "45": "r50", "46": "r50", "47": "r50", "48": "r50", "49": "r50", "50": "r50", "51": "r50", "52": "r50", "53": "r50", "54": "r50", "55": "r50", "57": "r50" }, { "25": "s12", "31": "s90" }, { "23": "r51", "24": "r51", "25": "r51", "26": "r51", "27": "r51", "28": "r51", "29": "r51", "30": "r51", "31": "r51", "32": "r51", "33": "r51", "34": "r51", "35": "r51", "36": "r51", "37": "r51", "38": "r51", "39": "r51", "40": "r51", "41": "r51", "42": "r51", "43": "r51", "44": "r51", "45": "r51", "46": "r51", "47": "r51", "48": "r51", "49": "r51", "50": "r51", "51": "r51", "52": "r51", "53": "r51", "54": "r51", "55": "r51", "57": "r51" }];

/**
 * Parsing stack.
 */
var stack = [];

/**
 * Tokenizer instance.
 */
var tokenizer = void 0;
/**
 * Generic tokenizer used by the parser in the Syntax tool.
 *
 * https://www.npmjs.com/package/syntax-cli
 *
 * See `--custom-tokinzer` to skip this generation, and use a custom one.
 */

var lexRules = [[/^#[^\n]+/, function () {/* skip comments */}], [/^\s+/, function () {/* skip whitespace */}], [/^-/, function () {
  return 'DASH';
}], [/^\//, function () {
  return 'CHAR';
}], [/^#/, function () {
  return 'CHAR';
}], [/^\|/, function () {
  return 'CHAR';
}], [/^\./, function () {
  return 'CHAR';
}], [/^\{/, function () {
  return 'CHAR';
}], [/^\{\d+\}/, function () {
  return 'RANGE_EXACT';
}], [/^\{\d+,\}/, function () {
  return 'RANGE_OPEN';
}], [/^\{\d+,\d+\}/, function () {
  return 'RANGE_CLOSED';
}], [/^\\k<(([\u0041-\u005a\u0061-\u007a\u00aa\u00b5\u00ba\u00c0-\u00d6\u00d8-\u00f6\u00f8-\u02c1\u02c6-\u02d1\u02e0-\u02e4\u02ec\u02ee\u0370-\u0374\u0376-\u0377\u037a-\u037d\u037f\u0386\u0388-\u038a\u038c\u038e-\u03a1\u03a3-\u03f5\u03f7-\u0481\u048a-\u052f\u0531-\u0556\u0559\u0560-\u0588\u05d0-\u05ea\u05ef-\u05f2\u0620-\u064a\u066e-\u066f\u0671-\u06d3\u06d5\u06e5-\u06e6\u06ee-\u06ef\u06fa-\u06fc\u06ff\u0710\u0712-\u072f\u074d-\u07a5\u07b1\u07ca-\u07ea\u07f4-\u07f5\u07fa\u0800-\u0815\u081a\u0824\u0828\u0840-\u0858\u0860-\u086a\u08a0-\u08b4\u08b6-\u08bd\u0904-\u0939\u093d\u0950\u0958-\u0961\u0971-\u0980\u0985-\u098c\u098f-\u0990\u0993-\u09a8\u09aa-\u09b0\u09b2\u09b6-\u09b9\u09bd\u09ce\u09dc-\u09dd\u09df-\u09e1\u09f0-\u09f1\u09fc\u0a05-\u0a0a\u0a0f-\u0a10\u0a13-\u0a28\u0a2a-\u0a30\u0a32-\u0a33\u0a35-\u0a36\u0a38-\u0a39\u0a59-\u0a5c\u0a5e\u0a72-\u0a74\u0a85-\u0a8d\u0a8f-\u0a91\u0a93-\u0aa8\u0aaa-\u0ab0\u0ab2-\u0ab3\u0ab5-\u0ab9\u0abd\u0ad0\u0ae0-\u0ae1\u0af9\u0b05-\u0b0c\u0b0f-\u0b10\u0b13-\u0b28\u0b2a-\u0b30\u0b32-\u0b33\u0b35-\u0b39\u0b3d\u0b5c-\u0b5d\u0b5f-\u0b61\u0b71\u0b83\u0b85-\u0b8a\u0b8e-\u0b90\u0b92-\u0b95\u0b99-\u0b9a\u0b9c\u0b9e-\u0b9f\u0ba3-\u0ba4\u0ba8-\u0baa\u0bae-\u0bb9\u0bd0\u0c05-\u0c0c\u0c0e-\u0c10\u0c12-\u0c28\u0c2a-\u0c39\u0c3d\u0c58-\u0c5a\u0c60-\u0c61\u0c80\u0c85-\u0c8c\u0c8e-\u0c90\u0c92-\u0ca8\u0caa-\u0cb3\u0cb5-\u0cb9\u0cbd\u0cde\u0ce0-\u0ce1\u0cf1-\u0cf2\u0d05-\u0d0c\u0d0e-\u0d10\u0d12-\u0d3a\u0d3d\u0d4e\u0d54-\u0d56\u0d5f-\u0d61\u0d7a-\u0d7f\u0d85-\u0d96\u0d9a-\u0db1\u0db3-\u0dbb\u0dbd\u0dc0-\u0dc6\u0e01-\u0e30\u0e32-\u0e33\u0e40-\u0e46\u0e81-\u0e82\u0e84\u0e86-\u0e8a\u0e8c-\u0ea3\u0ea5\u0ea7-\u0eb0\u0eb2-\u0eb3\u0ebd\u0ec0-\u0ec4\u0ec6\u0edc-\u0edf\u0f00\u0f40-\u0f47\u0f49-\u0f6c\u0f88-\u0f8c\u1000-\u102a\u103f\u1050-\u1055\u105a-\u105d\u1061\u1065-\u1066\u106e-\u1070\u1075-\u1081\u108e\u10a0-\u10c5\u10c7\u10cd\u10d0-\u10fa\u10fc-\u1248\u124a-\u124d\u1250-\u1256\u1258\u125a-\u125d\u1260-\u1288\u128a-\u128d\u1290-\u12b0\u12b2-\u12b5\u12b8-\u12be\u12c0\u12c2-\u12c5\u12c8-\u12d6\u12d8-\u1310\u1312-\u1315\u1318-\u135a\u1380-\u138f\u13a0-\u13f5\u13f8-\u13fd\u1401-\u166c\u166f-\u167f\u1681-\u169a\u16a0-\u16ea\u16ee-\u16f8\u1700-\u170c\u170e-\u1711\u1720-\u1731\u1740-\u1751\u1760-\u176c\u176e-\u1770\u1780-\u17b3\u17d7\u17dc\u1820-\u1878\u1880-\u18a8\u18aa\u18b0-\u18f5\u1900-\u191e\u1950-\u196d\u1970-\u1974\u1980-\u19ab\u19b0-\u19c9\u1a00-\u1a16\u1a20-\u1a54\u1aa7\u1b05-\u1b33\u1b45-\u1b4b\u1b83-\u1ba0\u1bae-\u1baf\u1bba-\u1be5\u1c00-\u1c23\u1c4d-\u1c4f\u1c5a-\u1c7d\u1c80-\u1c88\u1c90-\u1cba\u1cbd-\u1cbf\u1ce9-\u1cec\u1cee-\u1cf3\u1cf5-\u1cf6\u1cfa\u1d00-\u1dbf\u1e00-\u1f15\u1f18-\u1f1d\u1f20-\u1f45\u1f48-\u1f4d\u1f50-\u1f57\u1f59\u1f5b\u1f5d\u1f5f-\u1f7d\u1f80-\u1fb4\u1fb6-\u1fbc\u1fbe\u1fc2-\u1fc4\u1fc6-\u1fcc\u1fd0-\u1fd3\u1fd6-\u1fdb\u1fe0-\u1fec\u1ff2-\u1ff4\u1ff6-\u1ffc\u2071\u207f\u2090-\u209c\u2102\u2107\u210a-\u2113\u2115\u2118-\u211d\u2124\u2126\u2128\u212a-\u2139\u213c-\u213f\u2145-\u2149\u214e\u2160-\u2188\u2c00-\u2c2e\u2c30-\u2c5e\u2c60-\u2ce4\u2ceb-\u2cee\u2cf2-\u2cf3\u2d00-\u2d25\u2d27\u2d2d\u2d30-\u2d67\u2d6f\u2d80-\u2d96\u2da0-\u2da6\u2da8-\u2dae\u2db0-\u2db6\u2db8-\u2dbe\u2dc0-\u2dc6\u2dc8-\u2dce\u2dd0-\u2dd6\u2dd8-\u2dde\u3005-\u3007\u3021-\u3029\u3031-\u3035\u3038-\u303c\u3041-\u3096\u309b-\u309f\u30a1-\u30fa\u30fc-\u30ff\u3105-\u312f\u3131-\u318e\u31a0-\u31ba\u31f0-\u31ff\u3400-\u4db5\u4e00-\u9fef\ua000-\ua48c\ua4d0-\ua4fd\ua500-\ua60c\ua610-\ua61f\ua62a-\ua62b\ua640-\ua66e\ua67f-\ua69d\ua6a0-\ua6ef\ua717-\ua71f\ua722-\ua788\ua78b-\ua7bf\ua7c2-\ua7c6\ua7f7-\ua801\ua803-\ua805\ua807-\ua80a\ua80c-\ua822\ua840-\ua873\ua882-\ua8b3\ua8f2-\ua8f7\ua8fb\ua8fd-\ua8fe\ua90a-\ua925\ua930-\ua946\ua960-\ua97c\ua984-\ua9b2\ua9cf\ua9e0-\ua9e4\ua9e6-\ua9ef\ua9fa-\ua9fe\uaa00-\uaa28\uaa40-\uaa42\uaa44-\uaa4b\uaa60-\uaa76\uaa7a\uaa7e-\uaaaf\uaab1\uaab5-\uaab6\uaab9-\uaabd\uaac0\uaac2\uaadb-\uaadd\uaae0-\uaaea\uaaf2-\uaaf4\uab01-\uab06\uab09-\uab0e\uab11-\uab16\uab20-\uab26\uab28-\uab2e\uab30-\uab5a\uab5c-\uab67\uab70-\uabe2\uac00-\ud7a3\ud7b0-\ud7c6\ud7cb-\ud7fb\uf900-\ufa6d\ufa70-\ufad9\ufb00-\ufb06\ufb13-\ufb17\ufb1d\ufb1f-\ufb28\ufb2a-\ufb36\ufb38-\ufb3c\ufb3e\ufb40-\ufb41\ufb43-\ufb44\ufb46-\ufbb1\ufbd3-\ufd3d\ufd50-\ufd8f\ufd92-\ufdc7\ufdf0-\ufdfb\ufe70-\ufe74\ufe76-\ufefc\uff21-\uff3a\uff41-\uff5a\uff66-\uffbe\uffc2-\uffc7\uffca-\uffcf\uffd2-\uffd7\uffda-\uffdc]|\ud800[\udc00-\udc0b\udc0d-\udc26\udc28-\udc3a\udc3c-\udc3d\udc3f-\udc4d\udc50-\udc5d\udc80-\udcfa\udd40-\udd74\ude80-\ude9c\udea0-\uded0\udf00-\udf1f\udf2d-\udf4a\udf50-\udf75\udf80-\udf9d\udfa0-\udfc3\udfc8-\udfcf\udfd1-\udfd5]|\ud801[\udc00-\udc9d\udcb0-\udcd3\udcd8-\udcfb\udd00-\udd27\udd30-\udd63\ude00-\udf36\udf40-\udf55\udf60-\udf67]|\ud802[\udc00-\udc05\udc08\udc0a-\udc35\udc37-\udc38\udc3c\udc3f-\udc55\udc60-\udc76\udc80-\udc9e\udce0-\udcf2\udcf4-\udcf5\udd00-\udd15\udd20-\udd39\udd80-\uddb7\uddbe-\uddbf\ude00\ude10-\ude13\ude15-\ude17\ude19-\ude35\ude60-\ude7c\ude80-\ude9c\udec0-\udec7\udec9-\udee4\udf00-\udf35\udf40-\udf55\udf60-\udf72\udf80-\udf91]|\ud803[\udc00-\udc48\udc80-\udcb2\udcc0-\udcf2\udd00-\udd23\udf00-\udf1c\udf27\udf30-\udf45\udfe0-\udff6]|\ud804[\udc03-\udc37\udc83-\udcaf\udcd0-\udce8\udd03-\udd26\udd44\udd50-\udd72\udd76\udd83-\uddb2\uddc1-\uddc4\uddda\udddc\ude00-\ude11\ude13-\ude2b\ude80-\ude86\ude88\ude8a-\ude8d\ude8f-\ude9d\ude9f-\udea8\udeb0-\udede\udf05-\udf0c\udf0f-\udf10\udf13-\udf28\udf2a-\udf30\udf32-\udf33\udf35-\udf39\udf3d\udf50\udf5d-\udf61]|\ud805[\udc00-\udc34\udc47-\udc4a\udc5f\udc80-\udcaf\udcc4-\udcc5\udcc7\udd80-\uddae\uddd8-\udddb\ude00-\ude2f\ude44\ude80-\udeaa\udeb8\udf00-\udf1a]|\ud806[\udc00-\udc2b\udca0-\udcdf\udcff\udda0-\udda7\uddaa-\uddd0\udde1\udde3\ude00\ude0b-\ude32\ude3a\ude50\ude5c-\ude89\ude9d\udec0-\udef8]|\ud807[\udc00-\udc08\udc0a-\udc2e\udc40\udc72-\udc8f\udd00-\udd06\udd08-\udd09\udd0b-\udd30\udd46\udd60-\udd65\udd67-\udd68\udd6a-\udd89\udd98\udee0-\udef2]|\ud808[\udc00-\udf99]|\ud809[\udc00-\udc6e\udc80-\udd43]|\ud80c[\udc00-\udfff]|\ud80d[\udc00-\udc2e]|\ud811[\udc00-\ude46]|\ud81a[\udc00-\ude38\ude40-\ude5e\uded0-\udeed\udf00-\udf2f\udf40-\udf43\udf63-\udf77\udf7d-\udf8f]|\ud81b[\ude40-\ude7f\udf00-\udf4a\udf50\udf93-\udf9f\udfe0-\udfe1\udfe3]|\ud81c[\udc00-\udfff]|\ud81d[\udc00-\udfff]|\ud81e[\udc00-\udfff]|\ud81f[\udc00-\udfff]|\ud820[\udc00-\udfff]|\ud821[\udc00-\udff7]|\ud822[\udc00-\udef2]|\ud82c[\udc00-\udd1e\udd50-\udd52\udd64-\udd67\udd70-\udefb]|\ud82f[\udc00-\udc6a\udc70-\udc7c\udc80-\udc88\udc90-\udc99]|\ud835[\udc00-\udc54\udc56-\udc9c\udc9e-\udc9f\udca2\udca5-\udca6\udca9-\udcac\udcae-\udcb9\udcbb\udcbd-\udcc3\udcc5-\udd05\udd07-\udd0a\udd0d-\udd14\udd16-\udd1c\udd1e-\udd39\udd3b-\udd3e\udd40-\udd44\udd46\udd4a-\udd50\udd52-\udea5\udea8-\udec0\udec2-\udeda\udedc-\udefa\udefc-\udf14\udf16-\udf34\udf36-\udf4e\udf50-\udf6e\udf70-\udf88\udf8a-\udfa8\udfaa-\udfc2\udfc4-\udfcb]|\ud838[\udd00-\udd2c\udd37-\udd3d\udd4e\udec0-\udeeb]|\ud83a[\udc00-\udcc4\udd00-\udd43\udd4b]|\ud83b[\ude00-\ude03\ude05-\ude1f\ude21-\ude22\ude24\ude27\ude29-\ude32\ude34-\ude37\ude39\ude3b\ude42\ude47\ude49\ude4b\ude4d-\ude4f\ude51-\ude52\ude54\ude57\ude59\ude5b\ude5d\ude5f\ude61-\ude62\ude64\ude67-\ude6a\ude6c-\ude72\ude74-\ude77\ude79-\ude7c\ude7e\ude80-\ude89\ude8b-\ude9b\udea1-\udea3\udea5-\udea9\udeab-\udebb]|\ud840[\udc00-\udfff]|\ud841[\udc00-\udfff]|\ud842[\udc00-\udfff]|\ud843[\udc00-\udfff]|\ud844[\udc00-\udfff]|\ud845[\udc00-\udfff]|\ud846[\udc00-\udfff]|\ud847[\udc00-\udfff]|\ud848[\udc00-\udfff]|\ud849[\udc00-\udfff]|\ud84a[\udc00-\udfff]|\ud84b[\udc00-\udfff]|\ud84c[\udc00-\udfff]|\ud84d[\udc00-\udfff]|\ud84e[\udc00-\udfff]|\ud84f[\udc00-\udfff]|\ud850[\udc00-\udfff]|\ud851[\udc00-\udfff]|\ud852[\udc00-\udfff]|\ud853[\udc00-\udfff]|\ud854[\udc00-\udfff]|\ud855[\udc00-\udfff]|\ud856[\udc00-\udfff]|\ud857[\udc00-\udfff]|\ud858[\udc00-\udfff]|\ud859[\udc00-\udfff]|\ud85a[\udc00-\udfff]|\ud85b[\udc00-\udfff]|\ud85c[\udc00-\udfff]|\ud85d[\udc00-\udfff]|\ud85e[\udc00-\udfff]|\ud85f[\udc00-\udfff]|\ud860[\udc00-\udfff]|\ud861[\udc00-\udfff]|\ud862[\udc00-\udfff]|\ud863[\udc00-\udfff]|\ud864[\udc00-\udfff]|\ud865[\udc00-\udfff]|\ud866[\udc00-\udfff]|\ud867[\udc00-\udfff]|\ud868[\udc00-\udfff]|\ud869[\udc00-\uded6\udf00-\udfff]|\ud86a[\udc00-\udfff]|\ud86b[\udc00-\udfff]|\ud86c[\udc00-\udfff]|\ud86d[\udc00-\udf34\udf40-\udfff]|\ud86e[\udc00-\udc1d\udc20-\udfff]|\ud86f[\udc00-\udfff]|\ud870[\udc00-\udfff]|\ud871[\udc00-\udfff]|\ud872[\udc00-\udfff]|\ud873[\udc00-\udea1\udeb0-\udfff]|\ud874[\udc00-\udfff]|\ud875[\udc00-\udfff]|\ud876[\udc00-\udfff]|\ud877[\udc00-\udfff]|\ud878[\udc00-\udfff]|\ud879[\udc00-\udfff]|\ud87a[\udc00-\udfe0]|\ud87e[\udc00-\ude1d])|[$_]|(\\u[0-9a-fA-F]{4}|\\u\{[0-9a-fA-F]{1,}\}))(([\u0030-\u0039\u0041-\u005a\u005f\u0061-\u007a\u00aa\u00b5\u00b7\u00ba\u00c0-\u00d6\u00d8-\u00f6\u00f8-\u02c1\u02c6-\u02d1\u02e0-\u02e4\u02ec\u02ee\u0300-\u0374\u0376-\u0377\u037a-\u037d\u037f\u0386-\u038a\u038c\u038e-\u03a1\u03a3-\u03f5\u03f7-\u0481\u0483-\u0487\u048a-\u052f\u0531-\u0556\u0559\u0560-\u0588\u0591-\u05bd\u05bf\u05c1-\u05c2\u05c4-\u05c5\u05c7\u05d0-\u05ea\u05ef-\u05f2\u0610-\u061a\u0620-\u0669\u066e-\u06d3\u06d5-\u06dc\u06df-\u06e8\u06ea-\u06fc\u06ff\u0710-\u074a\u074d-\u07b1\u07c0-\u07f5\u07fa\u07fd\u0800-\u082d\u0840-\u085b\u0860-\u086a\u08a0-\u08b4\u08b6-\u08bd\u08d3-\u08e1\u08e3-\u0963\u0966-\u096f\u0971-\u0983\u0985-\u098c\u098f-\u0990\u0993-\u09a8\u09aa-\u09b0\u09b2\u09b6-\u09b9\u09bc-\u09c4\u09c7-\u09c8\u09cb-\u09ce\u09d7\u09dc-\u09dd\u09df-\u09e3\u09e6-\u09f1\u09fc\u09fe\u0a01-\u0a03\u0a05-\u0a0a\u0a0f-\u0a10\u0a13-\u0a28\u0a2a-\u0a30\u0a32-\u0a33\u0a35-\u0a36\u0a38-\u0a39\u0a3c\u0a3e-\u0a42\u0a47-\u0a48\u0a4b-\u0a4d\u0a51\u0a59-\u0a5c\u0a5e\u0a66-\u0a75\u0a81-\u0a83\u0a85-\u0a8d\u0a8f-\u0a91\u0a93-\u0aa8\u0aaa-\u0ab0\u0ab2-\u0ab3\u0ab5-\u0ab9\u0abc-\u0ac5\u0ac7-\u0ac9\u0acb-\u0acd\u0ad0\u0ae0-\u0ae3\u0ae6-\u0aef\u0af9-\u0aff\u0b01-\u0b03\u0b05-\u0b0c\u0b0f-\u0b10\u0b13-\u0b28\u0b2a-\u0b30\u0b32-\u0b33\u0b35-\u0b39\u0b3c-\u0b44\u0b47-\u0b48\u0b4b-\u0b4d\u0b56-\u0b57\u0b5c-\u0b5d\u0b5f-\u0b63\u0b66-\u0b6f\u0b71\u0b82-\u0b83\u0b85-\u0b8a\u0b8e-\u0b90\u0b92-\u0b95\u0b99-\u0b9a\u0b9c\u0b9e-\u0b9f\u0ba3-\u0ba4\u0ba8-\u0baa\u0bae-\u0bb9\u0bbe-\u0bc2\u0bc6-\u0bc8\u0bca-\u0bcd\u0bd0\u0bd7\u0be6-\u0bef\u0c00-\u0c0c\u0c0e-\u0c10\u0c12-\u0c28\u0c2a-\u0c39\u0c3d-\u0c44\u0c46-\u0c48\u0c4a-\u0c4d\u0c55-\u0c56\u0c58-\u0c5a\u0c60-\u0c63\u0c66-\u0c6f\u0c80-\u0c83\u0c85-\u0c8c\u0c8e-\u0c90\u0c92-\u0ca8\u0caa-\u0cb3\u0cb5-\u0cb9\u0cbc-\u0cc4\u0cc6-\u0cc8\u0cca-\u0ccd\u0cd5-\u0cd6\u0cde\u0ce0-\u0ce3\u0ce6-\u0cef\u0cf1-\u0cf2\u0d00-\u0d03\u0d05-\u0d0c\u0d0e-\u0d10\u0d12-\u0d44\u0d46-\u0d48\u0d4a-\u0d4e\u0d54-\u0d57\u0d5f-\u0d63\u0d66-\u0d6f\u0d7a-\u0d7f\u0d82-\u0d83\u0d85-\u0d96\u0d9a-\u0db1\u0db3-\u0dbb\u0dbd\u0dc0-\u0dc6\u0dca\u0dcf-\u0dd4\u0dd6\u0dd8-\u0ddf\u0de6-\u0def\u0df2-\u0df3\u0e01-\u0e3a\u0e40-\u0e4e\u0e50-\u0e59\u0e81-\u0e82\u0e84\u0e86-\u0e8a\u0e8c-\u0ea3\u0ea5\u0ea7-\u0ebd\u0ec0-\u0ec4\u0ec6\u0ec8-\u0ecd\u0ed0-\u0ed9\u0edc-\u0edf\u0f00\u0f18-\u0f19\u0f20-\u0f29\u0f35\u0f37\u0f39\u0f3e-\u0f47\u0f49-\u0f6c\u0f71-\u0f84\u0f86-\u0f97\u0f99-\u0fbc\u0fc6\u1000-\u1049\u1050-\u109d\u10a0-\u10c5\u10c7\u10cd\u10d0-\u10fa\u10fc-\u1248\u124a-\u124d\u1250-\u1256\u1258\u125a-\u125d\u1260-\u1288\u128a-\u128d\u1290-\u12b0\u12b2-\u12b5\u12b8-\u12be\u12c0\u12c2-\u12c5\u12c8-\u12d6\u12d8-\u1310\u1312-\u1315\u1318-\u135a\u135d-\u135f\u1369-\u1371\u1380-\u138f\u13a0-\u13f5\u13f8-\u13fd\u1401-\u166c\u166f-\u167f\u1681-\u169a\u16a0-\u16ea\u16ee-\u16f8\u1700-\u170c\u170e-\u1714\u1720-\u1734\u1740-\u1753\u1760-\u176c\u176e-\u1770\u1772-\u1773\u1780-\u17d3\u17d7\u17dc-\u17dd\u17e0-\u17e9\u180b-\u180d\u1810-\u1819\u1820-\u1878\u1880-\u18aa\u18b0-\u18f5\u1900-\u191e\u1920-\u192b\u1930-\u193b\u1946-\u196d\u1970-\u1974\u1980-\u19ab\u19b0-\u19c9\u19d0-\u19da\u1a00-\u1a1b\u1a20-\u1a5e\u1a60-\u1a7c\u1a7f-\u1a89\u1a90-\u1a99\u1aa7\u1ab0-\u1abd\u1b00-\u1b4b\u1b50-\u1b59\u1b6b-\u1b73\u1b80-\u1bf3\u1c00-\u1c37\u1c40-\u1c49\u1c4d-\u1c7d\u1c80-\u1c88\u1c90-\u1cba\u1cbd-\u1cbf\u1cd0-\u1cd2\u1cd4-\u1cfa\u1d00-\u1df9\u1dfb-\u1f15\u1f18-\u1f1d\u1f20-\u1f45\u1f48-\u1f4d\u1f50-\u1f57\u1f59\u1f5b\u1f5d\u1f5f-\u1f7d\u1f80-\u1fb4\u1fb6-\u1fbc\u1fbe\u1fc2-\u1fc4\u1fc6-\u1fcc\u1fd0-\u1fd3\u1fd6-\u1fdb\u1fe0-\u1fec\u1ff2-\u1ff4\u1ff6-\u1ffc\u203f-\u2040\u2054\u2071\u207f\u2090-\u209c\u20d0-\u20dc\u20e1\u20e5-\u20f0\u2102\u2107\u210a-\u2113\u2115\u2118-\u211d\u2124\u2126\u2128\u212a-\u2139\u213c-\u213f\u2145-\u2149\u214e\u2160-\u2188\u2c00-\u2c2e\u2c30-\u2c5e\u2c60-\u2ce4\u2ceb-\u2cf3\u2d00-\u2d25\u2d27\u2d2d\u2d30-\u2d67\u2d6f\u2d7f-\u2d96\u2da0-\u2da6\u2da8-\u2dae\u2db0-\u2db6\u2db8-\u2dbe\u2dc0-\u2dc6\u2dc8-\u2dce\u2dd0-\u2dd6\u2dd8-\u2dde\u2de0-\u2dff\u3005-\u3007\u3021-\u302f\u3031-\u3035\u3038-\u303c\u3041-\u3096\u3099-\u309f\u30a1-\u30fa\u30fc-\u30ff\u3105-\u312f\u3131-\u318e\u31a0-\u31ba\u31f0-\u31ff\u3400-\u4db5\u4e00-\u9fef\ua000-\ua48c\ua4d0-\ua4fd\ua500-\ua60c\ua610-\ua62b\ua640-\ua66f\ua674-\ua67d\ua67f-\ua6f1\ua717-\ua71f\ua722-\ua788\ua78b-\ua7bf\ua7c2-\ua7c6\ua7f7-\ua827\ua840-\ua873\ua880-\ua8c5\ua8d0-\ua8d9\ua8e0-\ua8f7\ua8fb\ua8fd-\ua92d\ua930-\ua953\ua960-\ua97c\ua980-\ua9c0\ua9cf-\ua9d9\ua9e0-\ua9fe\uaa00-\uaa36\uaa40-\uaa4d\uaa50-\uaa59\uaa60-\uaa76\uaa7a-\uaac2\uaadb-\uaadd\uaae0-\uaaef\uaaf2-\uaaf6\uab01-\uab06\uab09-\uab0e\uab11-\uab16\uab20-\uab26\uab28-\uab2e\uab30-\uab5a\uab5c-\uab67\uab70-\uabea\uabec-\uabed\uabf0-\uabf9\uac00-\ud7a3\ud7b0-\ud7c6\ud7cb-\ud7fb\uf900-\ufa6d\ufa70-\ufad9\ufb00-\ufb06\ufb13-\ufb17\ufb1d-\ufb28\ufb2a-\ufb36\ufb38-\ufb3c\ufb3e\ufb40-\ufb41\ufb43-\ufb44\ufb46-\ufbb1\ufbd3-\ufd3d\ufd50-\ufd8f\ufd92-\ufdc7\ufdf0-\ufdfb\ufe00-\ufe0f\ufe20-\ufe2f\ufe33-\ufe34\ufe4d-\ufe4f\ufe70-\ufe74\ufe76-\ufefc\uff10-\uff19\uff21-\uff3a\uff3f\uff41-\uff5a\uff66-\uffbe\uffc2-\uffc7\uffca-\uffcf\uffd2-\uffd7\uffda-\uffdc]|\ud800[\udc00-\udc0b\udc0d-\udc26\udc28-\udc3a\udc3c-\udc3d\udc3f-\udc4d\udc50-\udc5d\udc80-\udcfa\udd40-\udd74\uddfd\ude80-\ude9c\udea0-\uded0\udee0\udf00-\udf1f\udf2d-\udf4a\udf50-\udf7a\udf80-\udf9d\udfa0-\udfc3\udfc8-\udfcf\udfd1-\udfd5]|\ud801[\udc00-\udc9d\udca0-\udca9\udcb0-\udcd3\udcd8-\udcfb\udd00-\udd27\udd30-\udd63\ude00-\udf36\udf40-\udf55\udf60-\udf67]|\ud802[\udc00-\udc05\udc08\udc0a-\udc35\udc37-\udc38\udc3c\udc3f-\udc55\udc60-\udc76\udc80-\udc9e\udce0-\udcf2\udcf4-\udcf5\udd00-\udd15\udd20-\udd39\udd80-\uddb7\uddbe-\uddbf\ude00-\ude03\ude05-\ude06\ude0c-\ude13\ude15-\ude17\ude19-\ude35\ude38-\ude3a\ude3f\ude60-\ude7c\ude80-\ude9c\udec0-\udec7\udec9-\udee6\udf00-\udf35\udf40-\udf55\udf60-\udf72\udf80-\udf91]|\ud803[\udc00-\udc48\udc80-\udcb2\udcc0-\udcf2\udd00-\udd27\udd30-\udd39\udf00-\udf1c\udf27\udf30-\udf50\udfe0-\udff6]|\ud804[\udc00-\udc46\udc66-\udc6f\udc7f-\udcba\udcd0-\udce8\udcf0-\udcf9\udd00-\udd34\udd36-\udd3f\udd44-\udd46\udd50-\udd73\udd76\udd80-\uddc4\uddc9-\uddcc\uddd0-\uddda\udddc\ude00-\ude11\ude13-\ude37\ude3e\ude80-\ude86\ude88\ude8a-\ude8d\ude8f-\ude9d\ude9f-\udea8\udeb0-\udeea\udef0-\udef9\udf00-\udf03\udf05-\udf0c\udf0f-\udf10\udf13-\udf28\udf2a-\udf30\udf32-\udf33\udf35-\udf39\udf3b-\udf44\udf47-\udf48\udf4b-\udf4d\udf50\udf57\udf5d-\udf63\udf66-\udf6c\udf70-\udf74]|\ud805[\udc00-\udc4a\udc50-\udc59\udc5e-\udc5f\udc80-\udcc5\udcc7\udcd0-\udcd9\udd80-\uddb5\uddb8-\uddc0\uddd8-\udddd\ude00-\ude40\ude44\ude50-\ude59\ude80-\udeb8\udec0-\udec9\udf00-\udf1a\udf1d-\udf2b\udf30-\udf39]|\ud806[\udc00-\udc3a\udca0-\udce9\udcff\udda0-\udda7\uddaa-\uddd7\uddda-\udde1\udde3-\udde4\ude00-\ude3e\ude47\ude50-\ude99\ude9d\udec0-\udef8]|\ud807[\udc00-\udc08\udc0a-\udc36\udc38-\udc40\udc50-\udc59\udc72-\udc8f\udc92-\udca7\udca9-\udcb6\udd00-\udd06\udd08-\udd09\udd0b-\udd36\udd3a\udd3c-\udd3d\udd3f-\udd47\udd50-\udd59\udd60-\udd65\udd67-\udd68\udd6a-\udd8e\udd90-\udd91\udd93-\udd98\udda0-\udda9\udee0-\udef6]|\ud808[\udc00-\udf99]|\ud809[\udc00-\udc6e\udc80-\udd43]|\ud80c[\udc00-\udfff]|\ud80d[\udc00-\udc2e]|\ud811[\udc00-\ude46]|\ud81a[\udc00-\ude38\ude40-\ude5e\ude60-\ude69\uded0-\udeed\udef0-\udef4\udf00-\udf36\udf40-\udf43\udf50-\udf59\udf63-\udf77\udf7d-\udf8f]|\ud81b[\ude40-\ude7f\udf00-\udf4a\udf4f-\udf87\udf8f-\udf9f\udfe0-\udfe1\udfe3]|\ud81c[\udc00-\udfff]|\ud81d[\udc00-\udfff]|\ud81e[\udc00-\udfff]|\ud81f[\udc00-\udfff]|\ud820[\udc00-\udfff]|\ud821[\udc00-\udff7]|\ud822[\udc00-\udef2]|\ud82c[\udc00-\udd1e\udd50-\udd52\udd64-\udd67\udd70-\udefb]|\ud82f[\udc00-\udc6a\udc70-\udc7c\udc80-\udc88\udc90-\udc99\udc9d-\udc9e]|\ud834[\udd65-\udd69\udd6d-\udd72\udd7b-\udd82\udd85-\udd8b\uddaa-\uddad\ude42-\ude44]|\ud835[\udc00-\udc54\udc56-\udc9c\udc9e-\udc9f\udca2\udca5-\udca6\udca9-\udcac\udcae-\udcb9\udcbb\udcbd-\udcc3\udcc5-\udd05\udd07-\udd0a\udd0d-\udd14\udd16-\udd1c\udd1e-\udd39\udd3b-\udd3e\udd40-\udd44\udd46\udd4a-\udd50\udd52-\udea5\udea8-\udec0\udec2-\udeda\udedc-\udefa\udefc-\udf14\udf16-\udf34\udf36-\udf4e\udf50-\udf6e\udf70-\udf88\udf8a-\udfa8\udfaa-\udfc2\udfc4-\udfcb\udfce-\udfff]|\ud836[\ude00-\ude36\ude3b-\ude6c\ude75\ude84\ude9b-\ude9f\udea1-\udeaf]|\ud838[\udc00-\udc06\udc08-\udc18\udc1b-\udc21\udc23-\udc24\udc26-\udc2a\udd00-\udd2c\udd30-\udd3d\udd40-\udd49\udd4e\udec0-\udef9]|\ud83a[\udc00-\udcc4\udcd0-\udcd6\udd00-\udd4b\udd50-\udd59]|\ud83b[\ude00-\ude03\ude05-\ude1f\ude21-\ude22\ude24\ude27\ude29-\ude32\ude34-\ude37\ude39\ude3b\ude42\ude47\ude49\ude4b\ude4d-\ude4f\ude51-\ude52\ude54\ude57\ude59\ude5b\ude5d\ude5f\ude61-\ude62\ude64\ude67-\ude6a\ude6c-\ude72\ude74-\ude77\ude79-\ude7c\ude7e\ude80-\ude89\ude8b-\ude9b\udea1-\udea3\udea5-\udea9\udeab-\udebb]|\ud840[\udc00-\udfff]|\ud841[\udc00-\udfff]|\ud842[\udc00-\udfff]|\ud843[\udc00-\udfff]|\ud844[\udc00-\udfff]|\ud845[\udc00-\udfff]|\ud846[\udc00-\udfff]|\ud847[\udc00-\udfff]|\ud848[\udc00-\udfff]|\ud849[\udc00-\udfff]|\ud84a[\udc00-\udfff]|\ud84b[\udc00-\udfff]|\ud84c[\udc00-\udfff]|\ud84d[\udc00-\udfff]|\ud84e[\udc00-\udfff]|\ud84f[\udc00-\udfff]|\ud850[\udc00-\udfff]|\ud851[\udc00-\udfff]|\ud852[\udc00-\udfff]|\ud853[\udc00-\udfff]|\ud854[\udc00-\udfff]|\ud855[\udc00-\udfff]|\ud856[\udc00-\udfff]|\ud857[\udc00-\udfff]|\ud858[\udc00-\udfff]|\ud859[\udc00-\udfff]|\ud85a[\udc00-\udfff]|\ud85b[\udc00-\udfff]|\ud85c[\udc00-\udfff]|\ud85d[\udc00-\udfff]|\ud85e[\udc00-\udfff]|\ud85f[\udc00-\udfff]|\ud860[\udc00-\udfff]|\ud861[\udc00-\udfff]|\ud862[\udc00-\udfff]|\ud863[\udc00-\udfff]|\ud864[\udc00-\udfff]|\ud865[\udc00-\udfff]|\ud866[\udc00-\udfff]|\ud867[\udc00-\udfff]|\ud868[\udc00-\udfff]|\ud869[\udc00-\uded6\udf00-\udfff]|\ud86a[\udc00-\udfff]|\ud86b[\udc00-\udfff]|\ud86c[\udc00-\udfff]|\ud86d[\udc00-\udf34\udf40-\udfff]|\ud86e[\udc00-\udc1d\udc20-\udfff]|\ud86f[\udc00-\udfff]|\ud870[\udc00-\udfff]|\ud871[\udc00-\udfff]|\ud872[\udc00-\udfff]|\ud873[\udc00-\udea1\udeb0-\udfff]|\ud874[\udc00-\udfff]|\ud875[\udc00-\udfff]|\ud876[\udc00-\udfff]|\ud877[\udc00-\udfff]|\ud878[\udc00-\udfff]|\ud879[\udc00-\udfff]|\ud87a[\udc00-\udfe0]|\ud87e[\udc00-\ude1d]|\udb40[\udd00-\uddef])|[$_]|(\\u[0-9a-fA-F]{4}|\\u\{[0-9a-fA-F]{1,}\})|[\u200c\u200d])*>/, function () {
  var groupName = yytext.slice(3, -1);
  validateUnicodeGroupName(groupName, this.getCurrentState());
  return 'NAMED_GROUP_REF';
}], [/^\\b/, function () {
  return 'ESC_b';
}], [/^\\B/, function () {
  return 'ESC_B';
}], [/^\\c[a-zA-Z]/, function () {
  return 'CTRL_CH';
}], [/^\\0\d{1,2}/, function () {
  return 'OCT_CODE';
}], [/^\\0/, function () {
  return 'DEC_CODE';
}], [/^\\\d{1,3}/, function () {
  return 'DEC_CODE';
}], [/^\\u[dD][89abAB][0-9a-fA-F]{2}\\u[dD][c-fC-F][0-9a-fA-F]{2}/, function () {
  return 'U_CODE_SURROGATE';
}], [/^\\u\{[0-9a-fA-F]{1,}\}/, function () {
  return 'U_CODE';
}], [/^\\u[0-9a-fA-F]{4}/, function () {
  return 'U_CODE';
}], [/^\\[pP]\{\w+(?:=\w+)?\}/, function () {
  return 'U_PROP_VALUE_EXP';
}], [/^\\x[0-9a-fA-F]{2}/, function () {
  return 'HEX_CODE';
}], [/^\\[tnrdDsSwWvf]/, function () {
  return 'META_CHAR';
}], [/^\\\//, function () {
  return 'ESC_CHAR';
}], [/^\\[ #]/, function () {
  return 'ESC_CHAR';
}], [/^\\[\^\$\.\*\+\?\(\)\\\[\]\{\}\|\/]/, function () {
  return 'ESC_CHAR';
}], [/^\\[^*?+\[()\\|]/, function () {
  var s = this.getCurrentState();
  if (s === 'u_class' && yytext === "\\-") {
    return 'ESC_CHAR';
  } else if (s === 'u' || s === 'xu' || s === 'u_class') {
    throw new SyntaxError('invalid Unicode escape ' + yytext);
  }
  return 'ESC_CHAR';
}], [/^\(/, function () {
  return 'CHAR';
}], [/^\)/, function () {
  return 'CHAR';
}], [/^\(\?=/, function () {
  return 'POS_LA_ASSERT';
}], [/^\(\?!/, function () {
  return 'NEG_LA_ASSERT';
}], [/^\(\?<=/, function () {
  return 'POS_LB_ASSERT';
}], [/^\(\?<!/, function () {
  return 'NEG_LB_ASSERT';
}], [/^\(\?:/, function () {
  return 'NON_CAPTURE_GROUP';
}], [/^\(\?<(([\u0041-\u005a\u0061-\u007a\u00aa\u00b5\u00ba\u00c0-\u00d6\u00d8-\u00f6\u00f8-\u02c1\u02c6-\u02d1\u02e0-\u02e4\u02ec\u02ee\u0370-\u0374\u0376-\u0377\u037a-\u037d\u037f\u0386\u0388-\u038a\u038c\u038e-\u03a1\u03a3-\u03f5\u03f7-\u0481\u048a-\u052f\u0531-\u0556\u0559\u0560-\u0588\u05d0-\u05ea\u05ef-\u05f2\u0620-\u064a\u066e-\u066f\u0671-\u06d3\u06d5\u06e5-\u06e6\u06ee-\u06ef\u06fa-\u06fc\u06ff\u0710\u0712-\u072f\u074d-\u07a5\u07b1\u07ca-\u07ea\u07f4-\u07f5\u07fa\u0800-\u0815\u081a\u0824\u0828\u0840-\u0858\u0860-\u086a\u08a0-\u08b4\u08b6-\u08bd\u0904-\u0939\u093d\u0950\u0958-\u0961\u0971-\u0980\u0985-\u098c\u098f-\u0990\u0993-\u09a8\u09aa-\u09b0\u09b2\u09b6-\u09b9\u09bd\u09ce\u09dc-\u09dd\u09df-\u09e1\u09f0-\u09f1\u09fc\u0a05-\u0a0a\u0a0f-\u0a10\u0a13-\u0a28\u0a2a-\u0a30\u0a32-\u0a33\u0a35-\u0a36\u0a38-\u0a39\u0a59-\u0a5c\u0a5e\u0a72-\u0a74\u0a85-\u0a8d\u0a8f-\u0a91\u0a93-\u0aa8\u0aaa-\u0ab0\u0ab2-\u0ab3\u0ab5-\u0ab9\u0abd\u0ad0\u0ae0-\u0ae1\u0af9\u0b05-\u0b0c\u0b0f-\u0b10\u0b13-\u0b28\u0b2a-\u0b30\u0b32-\u0b33\u0b35-\u0b39\u0b3d\u0b5c-\u0b5d\u0b5f-\u0b61\u0b71\u0b83\u0b85-\u0b8a\u0b8e-\u0b90\u0b92-\u0b95\u0b99-\u0b9a\u0b9c\u0b9e-\u0b9f\u0ba3-\u0ba4\u0ba8-\u0baa\u0bae-\u0bb9\u0bd0\u0c05-\u0c0c\u0c0e-\u0c10\u0c12-\u0c28\u0c2a-\u0c39\u0c3d\u0c58-\u0c5a\u0c60-\u0c61\u0c80\u0c85-\u0c8c\u0c8e-\u0c90\u0c92-\u0ca8\u0caa-\u0cb3\u0cb5-\u0cb9\u0cbd\u0cde\u0ce0-\u0ce1\u0cf1-\u0cf2\u0d05-\u0d0c\u0d0e-\u0d10\u0d12-\u0d3a\u0d3d\u0d4e\u0d54-\u0d56\u0d5f-\u0d61\u0d7a-\u0d7f\u0d85-\u0d96\u0d9a-\u0db1\u0db3-\u0dbb\u0dbd\u0dc0-\u0dc6\u0e01-\u0e30\u0e32-\u0e33\u0e40-\u0e46\u0e81-\u0e82\u0e84\u0e86-\u0e8a\u0e8c-\u0ea3\u0ea5\u0ea7-\u0eb0\u0eb2-\u0eb3\u0ebd\u0ec0-\u0ec4\u0ec6\u0edc-\u0edf\u0f00\u0f40-\u0f47\u0f49-\u0f6c\u0f88-\u0f8c\u1000-\u102a\u103f\u1050-\u1055\u105a-\u105d\u1061\u1065-\u1066\u106e-\u1070\u1075-\u1081\u108e\u10a0-\u10c5\u10c7\u10cd\u10d0-\u10fa\u10fc-\u1248\u124a-\u124d\u1250-\u1256\u1258\u125a-\u125d\u1260-\u1288\u128a-\u128d\u1290-\u12b0\u12b2-\u12b5\u12b8-\u12be\u12c0\u12c2-\u12c5\u12c8-\u12d6\u12d8-\u1310\u1312-\u1315\u1318-\u135a\u1380-\u138f\u13a0-\u13f5\u13f8-\u13fd\u1401-\u166c\u166f-\u167f\u1681-\u169a\u16a0-\u16ea\u16ee-\u16f8\u1700-\u170c\u170e-\u1711\u1720-\u1731\u1740-\u1751\u1760-\u176c\u176e-\u1770\u1780-\u17b3\u17d7\u17dc\u1820-\u1878\u1880-\u18a8\u18aa\u18b0-\u18f5\u1900-\u191e\u1950-\u196d\u1970-\u1974\u1980-\u19ab\u19b0-\u19c9\u1a00-\u1a16\u1a20-\u1a54\u1aa7\u1b05-\u1b33\u1b45-\u1b4b\u1b83-\u1ba0\u1bae-\u1baf\u1bba-\u1be5\u1c00-\u1c23\u1c4d-\u1c4f\u1c5a-\u1c7d\u1c80-\u1c88\u1c90-\u1cba\u1cbd-\u1cbf\u1ce9-\u1cec\u1cee-\u1cf3\u1cf5-\u1cf6\u1cfa\u1d00-\u1dbf\u1e00-\u1f15\u1f18-\u1f1d\u1f20-\u1f45\u1f48-\u1f4d\u1f50-\u1f57\u1f59\u1f5b\u1f5d\u1f5f-\u1f7d\u1f80-\u1fb4\u1fb6-\u1fbc\u1fbe\u1fc2-\u1fc4\u1fc6-\u1fcc\u1fd0-\u1fd3\u1fd6-\u1fdb\u1fe0-\u1fec\u1ff2-\u1ff4\u1ff6-\u1ffc\u2071\u207f\u2090-\u209c\u2102\u2107\u210a-\u2113\u2115\u2118-\u211d\u2124\u2126\u2128\u212a-\u2139\u213c-\u213f\u2145-\u2149\u214e\u2160-\u2188\u2c00-\u2c2e\u2c30-\u2c5e\u2c60-\u2ce4\u2ceb-\u2cee\u2cf2-\u2cf3\u2d00-\u2d25\u2d27\u2d2d\u2d30-\u2d67\u2d6f\u2d80-\u2d96\u2da0-\u2da6\u2da8-\u2dae\u2db0-\u2db6\u2db8-\u2dbe\u2dc0-\u2dc6\u2dc8-\u2dce\u2dd0-\u2dd6\u2dd8-\u2dde\u3005-\u3007\u3021-\u3029\u3031-\u3035\u3038-\u303c\u3041-\u3096\u309b-\u309f\u30a1-\u30fa\u30fc-\u30ff\u3105-\u312f\u3131-\u318e\u31a0-\u31ba\u31f0-\u31ff\u3400-\u4db5\u4e00-\u9fef\ua000-\ua48c\ua4d0-\ua4fd\ua500-\ua60c\ua610-\ua61f\ua62a-\ua62b\ua640-\ua66e\ua67f-\ua69d\ua6a0-\ua6ef\ua717-\ua71f\ua722-\ua788\ua78b-\ua7bf\ua7c2-\ua7c6\ua7f7-\ua801\ua803-\ua805\ua807-\ua80a\ua80c-\ua822\ua840-\ua873\ua882-\ua8b3\ua8f2-\ua8f7\ua8fb\ua8fd-\ua8fe\ua90a-\ua925\ua930-\ua946\ua960-\ua97c\ua984-\ua9b2\ua9cf\ua9e0-\ua9e4\ua9e6-\ua9ef\ua9fa-\ua9fe\uaa00-\uaa28\uaa40-\uaa42\uaa44-\uaa4b\uaa60-\uaa76\uaa7a\uaa7e-\uaaaf\uaab1\uaab5-\uaab6\uaab9-\uaabd\uaac0\uaac2\uaadb-\uaadd\uaae0-\uaaea\uaaf2-\uaaf4\uab01-\uab06\uab09-\uab0e\uab11-\uab16\uab20-\uab26\uab28-\uab2e\uab30-\uab5a\uab5c-\uab67\uab70-\uabe2\uac00-\ud7a3\ud7b0-\ud7c6\ud7cb-\ud7fb\uf900-\ufa6d\ufa70-\ufad9\ufb00-\ufb06\ufb13-\ufb17\ufb1d\ufb1f-\ufb28\ufb2a-\ufb36\ufb38-\ufb3c\ufb3e\ufb40-\ufb41\ufb43-\ufb44\ufb46-\ufbb1\ufbd3-\ufd3d\ufd50-\ufd8f\ufd92-\ufdc7\ufdf0-\ufdfb\ufe70-\ufe74\ufe76-\ufefc\uff21-\uff3a\uff41-\uff5a\uff66-\uffbe\uffc2-\uffc7\uffca-\uffcf\uffd2-\uffd7\uffda-\uffdc]|\ud800[\udc00-\udc0b\udc0d-\udc26\udc28-\udc3a\udc3c-\udc3d\udc3f-\udc4d\udc50-\udc5d\udc80-\udcfa\udd40-\udd74\ude80-\ude9c\udea0-\uded0\udf00-\udf1f\udf2d-\udf4a\udf50-\udf75\udf80-\udf9d\udfa0-\udfc3\udfc8-\udfcf\udfd1-\udfd5]|\ud801[\udc00-\udc9d\udcb0-\udcd3\udcd8-\udcfb\udd00-\udd27\udd30-\udd63\ude00-\udf36\udf40-\udf55\udf60-\udf67]|\ud802[\udc00-\udc05\udc08\udc0a-\udc35\udc37-\udc38\udc3c\udc3f-\udc55\udc60-\udc76\udc80-\udc9e\udce0-\udcf2\udcf4-\udcf5\udd00-\udd15\udd20-\udd39\udd80-\uddb7\uddbe-\uddbf\ude00\ude10-\ude13\ude15-\ude17\ude19-\ude35\ude60-\ude7c\ude80-\ude9c\udec0-\udec7\udec9-\udee4\udf00-\udf35\udf40-\udf55\udf60-\udf72\udf80-\udf91]|\ud803[\udc00-\udc48\udc80-\udcb2\udcc0-\udcf2\udd00-\udd23\udf00-\udf1c\udf27\udf30-\udf45\udfe0-\udff6]|\ud804[\udc03-\udc37\udc83-\udcaf\udcd0-\udce8\udd03-\udd26\udd44\udd50-\udd72\udd76\udd83-\uddb2\uddc1-\uddc4\uddda\udddc\ude00-\ude11\ude13-\ude2b\ude80-\ude86\ude88\ude8a-\ude8d\ude8f-\ude9d\ude9f-\udea8\udeb0-\udede\udf05-\udf0c\udf0f-\udf10\udf13-\udf28\udf2a-\udf30\udf32-\udf33\udf35-\udf39\udf3d\udf50\udf5d-\udf61]|\ud805[\udc00-\udc34\udc47-\udc4a\udc5f\udc80-\udcaf\udcc4-\udcc5\udcc7\udd80-\uddae\uddd8-\udddb\ude00-\ude2f\ude44\ude80-\udeaa\udeb8\udf00-\udf1a]|\ud806[\udc00-\udc2b\udca0-\udcdf\udcff\udda0-\udda7\uddaa-\uddd0\udde1\udde3\ude00\ude0b-\ude32\ude3a\ude50\ude5c-\ude89\ude9d\udec0-\udef8]|\ud807[\udc00-\udc08\udc0a-\udc2e\udc40\udc72-\udc8f\udd00-\udd06\udd08-\udd09\udd0b-\udd30\udd46\udd60-\udd65\udd67-\udd68\udd6a-\udd89\udd98\udee0-\udef2]|\ud808[\udc00-\udf99]|\ud809[\udc00-\udc6e\udc80-\udd43]|\ud80c[\udc00-\udfff]|\ud80d[\udc00-\udc2e]|\ud811[\udc00-\ude46]|\ud81a[\udc00-\ude38\ude40-\ude5e\uded0-\udeed\udf00-\udf2f\udf40-\udf43\udf63-\udf77\udf7d-\udf8f]|\ud81b[\ude40-\ude7f\udf00-\udf4a\udf50\udf93-\udf9f\udfe0-\udfe1\udfe3]|\ud81c[\udc00-\udfff]|\ud81d[\udc00-\udfff]|\ud81e[\udc00-\udfff]|\ud81f[\udc00-\udfff]|\ud820[\udc00-\udfff]|\ud821[\udc00-\udff7]|\ud822[\udc00-\udef2]|\ud82c[\udc00-\udd1e\udd50-\udd52\udd64-\udd67\udd70-\udefb]|\ud82f[\udc00-\udc6a\udc70-\udc7c\udc80-\udc88\udc90-\udc99]|\ud835[\udc00-\udc54\udc56-\udc9c\udc9e-\udc9f\udca2\udca5-\udca6\udca9-\udcac\udcae-\udcb9\udcbb\udcbd-\udcc3\udcc5-\udd05\udd07-\udd0a\udd0d-\udd14\udd16-\udd1c\udd1e-\udd39\udd3b-\udd3e\udd40-\udd44\udd46\udd4a-\udd50\udd52-\udea5\udea8-\udec0\udec2-\udeda\udedc-\udefa\udefc-\udf14\udf16-\udf34\udf36-\udf4e\udf50-\udf6e\udf70-\udf88\udf8a-\udfa8\udfaa-\udfc2\udfc4-\udfcb]|\ud838[\udd00-\udd2c\udd37-\udd3d\udd4e\udec0-\udeeb]|\ud83a[\udc00-\udcc4\udd00-\udd43\udd4b]|\ud83b[\ude00-\ude03\ude05-\ude1f\ude21-\ude22\ude24\ude27\ude29-\ude32\ude34-\ude37\ude39\ude3b\ude42\ude47\ude49\ude4b\ude4d-\ude4f\ude51-\ude52\ude54\ude57\ude59\ude5b\ude5d\ude5f\ude61-\ude62\ude64\ude67-\ude6a\ude6c-\ude72\ude74-\ude77\ude79-\ude7c\ude7e\ude80-\ude89\ude8b-\ude9b\udea1-\udea3\udea5-\udea9\udeab-\udebb]|\ud840[\udc00-\udfff]|\ud841[\udc00-\udfff]|\ud842[\udc00-\udfff]|\ud843[\udc00-\udfff]|\ud844[\udc00-\udfff]|\ud845[\udc00-\udfff]|\ud846[\udc00-\udfff]|\ud847[\udc00-\udfff]|\ud848[\udc00-\udfff]|\ud849[\udc00-\udfff]|\ud84a[\udc00-\udfff]|\ud84b[\udc00-\udfff]|\ud84c[\udc00-\udfff]|\ud84d[\udc00-\udfff]|\ud84e[\udc00-\udfff]|\ud84f[\udc00-\udfff]|\ud850[\udc00-\udfff]|\ud851[\udc00-\udfff]|\ud852[\udc00-\udfff]|\ud853[\udc00-\udfff]|\ud854[\udc00-\udfff]|\ud855[\udc00-\udfff]|\ud856[\udc00-\udfff]|\ud857[\udc00-\udfff]|\ud858[\udc00-\udfff]|\ud859[\udc00-\udfff]|\ud85a[\udc00-\udfff]|\ud85b[\udc00-\udfff]|\ud85c[\udc00-\udfff]|\ud85d[\udc00-\udfff]|\ud85e[\udc00-\udfff]|\ud85f[\udc00-\udfff]|\ud860[\udc00-\udfff]|\ud861[\udc00-\udfff]|\ud862[\udc00-\udfff]|\ud863[\udc00-\udfff]|\ud864[\udc00-\udfff]|\ud865[\udc00-\udfff]|\ud866[\udc00-\udfff]|\ud867[\udc00-\udfff]|\ud868[\udc00-\udfff]|\ud869[\udc00-\uded6\udf00-\udfff]|\ud86a[\udc00-\udfff]|\ud86b[\udc00-\udfff]|\ud86c[\udc00-\udfff]|\ud86d[\udc00-\udf34\udf40-\udfff]|\ud86e[\udc00-\udc1d\udc20-\udfff]|\ud86f[\udc00-\udfff]|\ud870[\udc00-\udfff]|\ud871[\udc00-\udfff]|\ud872[\udc00-\udfff]|\ud873[\udc00-\udea1\udeb0-\udfff]|\ud874[\udc00-\udfff]|\ud875[\udc00-\udfff]|\ud876[\udc00-\udfff]|\ud877[\udc00-\udfff]|\ud878[\udc00-\udfff]|\ud879[\udc00-\udfff]|\ud87a[\udc00-\udfe0]|\ud87e[\udc00-\ude1d])|[$_]|(\\u[0-9a-fA-F]{4}|\\u\{[0-9a-fA-F]{1,}\}))(([\u0030-\u0039\u0041-\u005a\u005f\u0061-\u007a\u00aa\u00b5\u00b7\u00ba\u00c0-\u00d6\u00d8-\u00f6\u00f8-\u02c1\u02c6-\u02d1\u02e0-\u02e4\u02ec\u02ee\u0300-\u0374\u0376-\u0377\u037a-\u037d\u037f\u0386-\u038a\u038c\u038e-\u03a1\u03a3-\u03f5\u03f7-\u0481\u0483-\u0487\u048a-\u052f\u0531-\u0556\u0559\u0560-\u0588\u0591-\u05bd\u05bf\u05c1-\u05c2\u05c4-\u05c5\u05c7\u05d0-\u05ea\u05ef-\u05f2\u0610-\u061a\u0620-\u0669\u066e-\u06d3\u06d5-\u06dc\u06df-\u06e8\u06ea-\u06fc\u06ff\u0710-\u074a\u074d-\u07b1\u07c0-\u07f5\u07fa\u07fd\u0800-\u082d\u0840-\u085b\u0860-\u086a\u08a0-\u08b4\u08b6-\u08bd\u08d3-\u08e1\u08e3-\u0963\u0966-\u096f\u0971-\u0983\u0985-\u098c\u098f-\u0990\u0993-\u09a8\u09aa-\u09b0\u09b2\u09b6-\u09b9\u09bc-\u09c4\u09c7-\u09c8\u09cb-\u09ce\u09d7\u09dc-\u09dd\u09df-\u09e3\u09e6-\u09f1\u09fc\u09fe\u0a01-\u0a03\u0a05-\u0a0a\u0a0f-\u0a10\u0a13-\u0a28\u0a2a-\u0a30\u0a32-\u0a33\u0a35-\u0a36\u0a38-\u0a39\u0a3c\u0a3e-\u0a42\u0a47-\u0a48\u0a4b-\u0a4d\u0a51\u0a59-\u0a5c\u0a5e\u0a66-\u0a75\u0a81-\u0a83\u0a85-\u0a8d\u0a8f-\u0a91\u0a93-\u0aa8\u0aaa-\u0ab0\u0ab2-\u0ab3\u0ab5-\u0ab9\u0abc-\u0ac5\u0ac7-\u0ac9\u0acb-\u0acd\u0ad0\u0ae0-\u0ae3\u0ae6-\u0aef\u0af9-\u0aff\u0b01-\u0b03\u0b05-\u0b0c\u0b0f-\u0b10\u0b13-\u0b28\u0b2a-\u0b30\u0b32-\u0b33\u0b35-\u0b39\u0b3c-\u0b44\u0b47-\u0b48\u0b4b-\u0b4d\u0b56-\u0b57\u0b5c-\u0b5d\u0b5f-\u0b63\u0b66-\u0b6f\u0b71\u0b82-\u0b83\u0b85-\u0b8a\u0b8e-\u0b90\u0b92-\u0b95\u0b99-\u0b9a\u0b9c\u0b9e-\u0b9f\u0ba3-\u0ba4\u0ba8-\u0baa\u0bae-\u0bb9\u0bbe-\u0bc2\u0bc6-\u0bc8\u0bca-\u0bcd\u0bd0\u0bd7\u0be6-\u0bef\u0c00-\u0c0c\u0c0e-\u0c10\u0c12-\u0c28\u0c2a-\u0c39\u0c3d-\u0c44\u0c46-\u0c48\u0c4a-\u0c4d\u0c55-\u0c56\u0c58-\u0c5a\u0c60-\u0c63\u0c66-\u0c6f\u0c80-\u0c83\u0c85-\u0c8c\u0c8e-\u0c90\u0c92-\u0ca8\u0caa-\u0cb3\u0cb5-\u0cb9\u0cbc-\u0cc4\u0cc6-\u0cc8\u0cca-\u0ccd\u0cd5-\u0cd6\u0cde\u0ce0-\u0ce3\u0ce6-\u0cef\u0cf1-\u0cf2\u0d00-\u0d03\u0d05-\u0d0c\u0d0e-\u0d10\u0d12-\u0d44\u0d46-\u0d48\u0d4a-\u0d4e\u0d54-\u0d57\u0d5f-\u0d63\u0d66-\u0d6f\u0d7a-\u0d7f\u0d82-\u0d83\u0d85-\u0d96\u0d9a-\u0db1\u0db3-\u0dbb\u0dbd\u0dc0-\u0dc6\u0dca\u0dcf-\u0dd4\u0dd6\u0dd8-\u0ddf\u0de6-\u0def\u0df2-\u0df3\u0e01-\u0e3a\u0e40-\u0e4e\u0e50-\u0e59\u0e81-\u0e82\u0e84\u0e86-\u0e8a\u0e8c-\u0ea3\u0ea5\u0ea7-\u0ebd\u0ec0-\u0ec4\u0ec6\u0ec8-\u0ecd\u0ed0-\u0ed9\u0edc-\u0edf\u0f00\u0f18-\u0f19\u0f20-\u0f29\u0f35\u0f37\u0f39\u0f3e-\u0f47\u0f49-\u0f6c\u0f71-\u0f84\u0f86-\u0f97\u0f99-\u0fbc\u0fc6\u1000-\u1049\u1050-\u109d\u10a0-\u10c5\u10c7\u10cd\u10d0-\u10fa\u10fc-\u1248\u124a-\u124d\u1250-\u1256\u1258\u125a-\u125d\u1260-\u1288\u128a-\u128d\u1290-\u12b0\u12b2-\u12b5\u12b8-\u12be\u12c0\u12c2-\u12c5\u12c8-\u12d6\u12d8-\u1310\u1312-\u1315\u1318-\u135a\u135d-\u135f\u1369-\u1371\u1380-\u138f\u13a0-\u13f5\u13f8-\u13fd\u1401-\u166c\u166f-\u167f\u1681-\u169a\u16a0-\u16ea\u16ee-\u16f8\u1700-\u170c\u170e-\u1714\u1720-\u1734\u1740-\u1753\u1760-\u176c\u176e-\u1770\u1772-\u1773\u1780-\u17d3\u17d7\u17dc-\u17dd\u17e0-\u17e9\u180b-\u180d\u1810-\u1819\u1820-\u1878\u1880-\u18aa\u18b0-\u18f5\u1900-\u191e\u1920-\u192b\u1930-\u193b\u1946-\u196d\u1970-\u1974\u1980-\u19ab\u19b0-\u19c9\u19d0-\u19da\u1a00-\u1a1b\u1a20-\u1a5e\u1a60-\u1a7c\u1a7f-\u1a89\u1a90-\u1a99\u1aa7\u1ab0-\u1abd\u1b00-\u1b4b\u1b50-\u1b59\u1b6b-\u1b73\u1b80-\u1bf3\u1c00-\u1c37\u1c40-\u1c49\u1c4d-\u1c7d\u1c80-\u1c88\u1c90-\u1cba\u1cbd-\u1cbf\u1cd0-\u1cd2\u1cd4-\u1cfa\u1d00-\u1df9\u1dfb-\u1f15\u1f18-\u1f1d\u1f20-\u1f45\u1f48-\u1f4d\u1f50-\u1f57\u1f59\u1f5b\u1f5d\u1f5f-\u1f7d\u1f80-\u1fb4\u1fb6-\u1fbc\u1fbe\u1fc2-\u1fc4\u1fc6-\u1fcc\u1fd0-\u1fd3\u1fd6-\u1fdb\u1fe0-\u1fec\u1ff2-\u1ff4\u1ff6-\u1ffc\u203f-\u2040\u2054\u2071\u207f\u2090-\u209c\u20d0-\u20dc\u20e1\u20e5-\u20f0\u2102\u2107\u210a-\u2113\u2115\u2118-\u211d\u2124\u2126\u2128\u212a-\u2139\u213c-\u213f\u2145-\u2149\u214e\u2160-\u2188\u2c00-\u2c2e\u2c30-\u2c5e\u2c60-\u2ce4\u2ceb-\u2cf3\u2d00-\u2d25\u2d27\u2d2d\u2d30-\u2d67\u2d6f\u2d7f-\u2d96\u2da0-\u2da6\u2da8-\u2dae\u2db0-\u2db6\u2db8-\u2dbe\u2dc0-\u2dc6\u2dc8-\u2dce\u2dd0-\u2dd6\u2dd8-\u2dde\u2de0-\u2dff\u3005-\u3007\u3021-\u302f\u3031-\u3035\u3038-\u303c\u3041-\u3096\u3099-\u309f\u30a1-\u30fa\u30fc-\u30ff\u3105-\u312f\u3131-\u318e\u31a0-\u31ba\u31f0-\u31ff\u3400-\u4db5\u4e00-\u9fef\ua000-\ua48c\ua4d0-\ua4fd\ua500-\ua60c\ua610-\ua62b\ua640-\ua66f\ua674-\ua67d\ua67f-\ua6f1\ua717-\ua71f\ua722-\ua788\ua78b-\ua7bf\ua7c2-\ua7c6\ua7f7-\ua827\ua840-\ua873\ua880-\ua8c5\ua8d0-\ua8d9\ua8e0-\ua8f7\ua8fb\ua8fd-\ua92d\ua930-\ua953\ua960-\ua97c\ua980-\ua9c0\ua9cf-\ua9d9\ua9e0-\ua9fe\uaa00-\uaa36\uaa40-\uaa4d\uaa50-\uaa59\uaa60-\uaa76\uaa7a-\uaac2\uaadb-\uaadd\uaae0-\uaaef\uaaf2-\uaaf6\uab01-\uab06\uab09-\uab0e\uab11-\uab16\uab20-\uab26\uab28-\uab2e\uab30-\uab5a\uab5c-\uab67\uab70-\uabea\uabec-\uabed\uabf0-\uabf9\uac00-\ud7a3\ud7b0-\ud7c6\ud7cb-\ud7fb\uf900-\ufa6d\ufa70-\ufad9\ufb00-\ufb06\ufb13-\ufb17\ufb1d-\ufb28\ufb2a-\ufb36\ufb38-\ufb3c\ufb3e\ufb40-\ufb41\ufb43-\ufb44\ufb46-\ufbb1\ufbd3-\ufd3d\ufd50-\ufd8f\ufd92-\ufdc7\ufdf0-\ufdfb\ufe00-\ufe0f\ufe20-\ufe2f\ufe33-\ufe34\ufe4d-\ufe4f\ufe70-\ufe74\ufe76-\ufefc\uff10-\uff19\uff21-\uff3a\uff3f\uff41-\uff5a\uff66-\uffbe\uffc2-\uffc7\uffca-\uffcf\uffd2-\uffd7\uffda-\uffdc]|\ud800[\udc00-\udc0b\udc0d-\udc26\udc28-\udc3a\udc3c-\udc3d\udc3f-\udc4d\udc50-\udc5d\udc80-\udcfa\udd40-\udd74\uddfd\ude80-\ude9c\udea0-\uded0\udee0\udf00-\udf1f\udf2d-\udf4a\udf50-\udf7a\udf80-\udf9d\udfa0-\udfc3\udfc8-\udfcf\udfd1-\udfd5]|\ud801[\udc00-\udc9d\udca0-\udca9\udcb0-\udcd3\udcd8-\udcfb\udd00-\udd27\udd30-\udd63\ude00-\udf36\udf40-\udf55\udf60-\udf67]|\ud802[\udc00-\udc05\udc08\udc0a-\udc35\udc37-\udc38\udc3c\udc3f-\udc55\udc60-\udc76\udc80-\udc9e\udce0-\udcf2\udcf4-\udcf5\udd00-\udd15\udd20-\udd39\udd80-\uddb7\uddbe-\uddbf\ude00-\ude03\ude05-\ude06\ude0c-\ude13\ude15-\ude17\ude19-\ude35\ude38-\ude3a\ude3f\ude60-\ude7c\ude80-\ude9c\udec0-\udec7\udec9-\udee6\udf00-\udf35\udf40-\udf55\udf60-\udf72\udf80-\udf91]|\ud803[\udc00-\udc48\udc80-\udcb2\udcc0-\udcf2\udd00-\udd27\udd30-\udd39\udf00-\udf1c\udf27\udf30-\udf50\udfe0-\udff6]|\ud804[\udc00-\udc46\udc66-\udc6f\udc7f-\udcba\udcd0-\udce8\udcf0-\udcf9\udd00-\udd34\udd36-\udd3f\udd44-\udd46\udd50-\udd73\udd76\udd80-\uddc4\uddc9-\uddcc\uddd0-\uddda\udddc\ude00-\ude11\ude13-\ude37\ude3e\ude80-\ude86\ude88\ude8a-\ude8d\ude8f-\ude9d\ude9f-\udea8\udeb0-\udeea\udef0-\udef9\udf00-\udf03\udf05-\udf0c\udf0f-\udf10\udf13-\udf28\udf2a-\udf30\udf32-\udf33\udf35-\udf39\udf3b-\udf44\udf47-\udf48\udf4b-\udf4d\udf50\udf57\udf5d-\udf63\udf66-\udf6c\udf70-\udf74]|\ud805[\udc00-\udc4a\udc50-\udc59\udc5e-\udc5f\udc80-\udcc5\udcc7\udcd0-\udcd9\udd80-\uddb5\uddb8-\uddc0\uddd8-\udddd\ude00-\ude40\ude44\ude50-\ude59\ude80-\udeb8\udec0-\udec9\udf00-\udf1a\udf1d-\udf2b\udf30-\udf39]|\ud806[\udc00-\udc3a\udca0-\udce9\udcff\udda0-\udda7\uddaa-\uddd7\uddda-\udde1\udde3-\udde4\ude00-\ude3e\ude47\ude50-\ude99\ude9d\udec0-\udef8]|\ud807[\udc00-\udc08\udc0a-\udc36\udc38-\udc40\udc50-\udc59\udc72-\udc8f\udc92-\udca7\udca9-\udcb6\udd00-\udd06\udd08-\udd09\udd0b-\udd36\udd3a\udd3c-\udd3d\udd3f-\udd47\udd50-\udd59\udd60-\udd65\udd67-\udd68\udd6a-\udd8e\udd90-\udd91\udd93-\udd98\udda0-\udda9\udee0-\udef6]|\ud808[\udc00-\udf99]|\ud809[\udc00-\udc6e\udc80-\udd43]|\ud80c[\udc00-\udfff]|\ud80d[\udc00-\udc2e]|\ud811[\udc00-\ude46]|\ud81a[\udc00-\ude38\ude40-\ude5e\ude60-\ude69\uded0-\udeed\udef0-\udef4\udf00-\udf36\udf40-\udf43\udf50-\udf59\udf63-\udf77\udf7d-\udf8f]|\ud81b[\ude40-\ude7f\udf00-\udf4a\udf4f-\udf87\udf8f-\udf9f\udfe0-\udfe1\udfe3]|\ud81c[\udc00-\udfff]|\ud81d[\udc00-\udfff]|\ud81e[\udc00-\udfff]|\ud81f[\udc00-\udfff]|\ud820[\udc00-\udfff]|\ud821[\udc00-\udff7]|\ud822[\udc00-\udef2]|\ud82c[\udc00-\udd1e\udd50-\udd52\udd64-\udd67\udd70-\udefb]|\ud82f[\udc00-\udc6a\udc70-\udc7c\udc80-\udc88\udc90-\udc99\udc9d-\udc9e]|\ud834[\udd65-\udd69\udd6d-\udd72\udd7b-\udd82\udd85-\udd8b\uddaa-\uddad\ude42-\ude44]|\ud835[\udc00-\udc54\udc56-\udc9c\udc9e-\udc9f\udca2\udca5-\udca6\udca9-\udcac\udcae-\udcb9\udcbb\udcbd-\udcc3\udcc5-\udd05\udd07-\udd0a\udd0d-\udd14\udd16-\udd1c\udd1e-\udd39\udd3b-\udd3e\udd40-\udd44\udd46\udd4a-\udd50\udd52-\udea5\udea8-\udec0\udec2-\udeda\udedc-\udefa\udefc-\udf14\udf16-\udf34\udf36-\udf4e\udf50-\udf6e\udf70-\udf88\udf8a-\udfa8\udfaa-\udfc2\udfc4-\udfcb\udfce-\udfff]|\ud836[\ude00-\ude36\ude3b-\ude6c\ude75\ude84\ude9b-\ude9f\udea1-\udeaf]|\ud838[\udc00-\udc06\udc08-\udc18\udc1b-\udc21\udc23-\udc24\udc26-\udc2a\udd00-\udd2c\udd30-\udd3d\udd40-\udd49\udd4e\udec0-\udef9]|\ud83a[\udc00-\udcc4\udcd0-\udcd6\udd00-\udd4b\udd50-\udd59]|\ud83b[\ude00-\ude03\ude05-\ude1f\ude21-\ude22\ude24\ude27\ude29-\ude32\ude34-\ude37\ude39\ude3b\ude42\ude47\ude49\ude4b\ude4d-\ude4f\ude51-\ude52\ude54\ude57\ude59\ude5b\ude5d\ude5f\ude61-\ude62\ude64\ude67-\ude6a\ude6c-\ude72\ude74-\ude77\ude79-\ude7c\ude7e\ude80-\ude89\ude8b-\ude9b\udea1-\udea3\udea5-\udea9\udeab-\udebb]|\ud840[\udc00-\udfff]|\ud841[\udc00-\udfff]|\ud842[\udc00-\udfff]|\ud843[\udc00-\udfff]|\ud844[\udc00-\udfff]|\ud845[\udc00-\udfff]|\ud846[\udc00-\udfff]|\ud847[\udc00-\udfff]|\ud848[\udc00-\udfff]|\ud849[\udc00-\udfff]|\ud84a[\udc00-\udfff]|\ud84b[\udc00-\udfff]|\ud84c[\udc00-\udfff]|\ud84d[\udc00-\udfff]|\ud84e[\udc00-\udfff]|\ud84f[\udc00-\udfff]|\ud850[\udc00-\udfff]|\ud851[\udc00-\udfff]|\ud852[\udc00-\udfff]|\ud853[\udc00-\udfff]|\ud854[\udc00-\udfff]|\ud855[\udc00-\udfff]|\ud856[\udc00-\udfff]|\ud857[\udc00-\udfff]|\ud858[\udc00-\udfff]|\ud859[\udc00-\udfff]|\ud85a[\udc00-\udfff]|\ud85b[\udc00-\udfff]|\ud85c[\udc00-\udfff]|\ud85d[\udc00-\udfff]|\ud85e[\udc00-\udfff]|\ud85f[\udc00-\udfff]|\ud860[\udc00-\udfff]|\ud861[\udc00-\udfff]|\ud862[\udc00-\udfff]|\ud863[\udc00-\udfff]|\ud864[\udc00-\udfff]|\ud865[\udc00-\udfff]|\ud866[\udc00-\udfff]|\ud867[\udc00-\udfff]|\ud868[\udc00-\udfff]|\ud869[\udc00-\uded6\udf00-\udfff]|\ud86a[\udc00-\udfff]|\ud86b[\udc00-\udfff]|\ud86c[\udc00-\udfff]|\ud86d[\udc00-\udf34\udf40-\udfff]|\ud86e[\udc00-\udc1d\udc20-\udfff]|\ud86f[\udc00-\udfff]|\ud870[\udc00-\udfff]|\ud871[\udc00-\udfff]|\ud872[\udc00-\udfff]|\ud873[\udc00-\udea1\udeb0-\udfff]|\ud874[\udc00-\udfff]|\ud875[\udc00-\udfff]|\ud876[\udc00-\udfff]|\ud877[\udc00-\udfff]|\ud878[\udc00-\udfff]|\ud879[\udc00-\udfff]|\ud87a[\udc00-\udfe0]|\ud87e[\udc00-\ude1d]|\udb40[\udd00-\uddef])|[$_]|(\\u[0-9a-fA-F]{4}|\\u\{[0-9a-fA-F]{1,}\})|[\u200c\u200d])*>/, function () {
  yytext = yytext.slice(3, -1);
  validateUnicodeGroupName(yytext, this.getCurrentState());
  return 'NAMED_CAPTURE_GROUP';
}], [/^\(/, function () {
  return 'L_PAREN';
}], [/^\)/, function () {
  return 'R_PAREN';
}], [/^[*?+[^$]/, function () {
  return 'CHAR';
}], [/^\\\]/, function () {
  return 'ESC_CHAR';
}], [/^\]/, function () {
  this.popState();return 'R_BRACKET';
}], [/^\^/, function () {
  return 'BOS';
}], [/^\$/, function () {
  return 'EOS';
}], [/^\*/, function () {
  return 'STAR';
}], [/^\?/, function () {
  return 'Q_MARK';
}], [/^\+/, function () {
  return 'PLUS';
}], [/^\|/, function () {
  return 'BAR';
}], [/^\./, function () {
  return 'ANY';
}], [/^\//, function () {
  return 'SLASH';
}], [/^[^*?+\[()\\|]/, function () {
  return 'CHAR';
}], [/^\[\^/, function () {
  var s = this.getCurrentState();this.pushState(s === 'u' || s === 'xu' ? 'u_class' : 'class');return 'NEG_CLASS';
}], [/^\[/, function () {
  var s = this.getCurrentState();this.pushState(s === 'u' || s === 'xu' ? 'u_class' : 'class');return 'L_BRACKET';
}]];
var lexRulesByConditions = { "INITIAL": [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 20, 22, 23, 24, 26, 27, 30, 31, 32, 33, 34, 35, 36, 37, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51], "u": [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 27, 30, 31, 32, 33, 34, 35, 36, 37, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51], "xu": [0, 1, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 30, 31, 32, 33, 34, 35, 36, 37, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51], "x": [0, 1, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 20, 22, 23, 24, 26, 27, 30, 31, 32, 33, 34, 35, 36, 37, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51], "u_class": [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51], "class": [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 20, 22, 23, 24, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51] };

var EOF_TOKEN = {
  type: EOF,
  value: ''
};

tokenizer = {
  initString: function initString(string) {
    this._string = string;
    this._cursor = 0;

    this._states = ['INITIAL'];
    this._tokensQueue = [];

    this._currentLine = 1;
    this._currentColumn = 0;
    this._currentLineBeginOffset = 0;

    /**
     * Matched token location data.
     */
    this._tokenStartOffset = 0;
    this._tokenEndOffset = 0;
    this._tokenStartLine = 1;
    this._tokenEndLine = 1;
    this._tokenStartColumn = 0;
    this._tokenEndColumn = 0;

    return this;
  },


  /**
   * Returns tokenizer states.
   */
  getStates: function getStates() {
    return this._states;
  },
  getCurrentState: function getCurrentState() {
    return this._states[this._states.length - 1];
  },
  pushState: function pushState(state) {
    this._states.push(state);
  },
  begin: function begin(state) {
    this.pushState(state);
  },
  popState: function popState() {
    if (this._states.length > 1) {
      return this._states.pop();
    }
    return this._states[0];
  },
  getNextToken: function getNextToken() {
    // Something was queued, return it.
    if (this._tokensQueue.length > 0) {
      return this.onToken(this._toToken(this._tokensQueue.shift()));
    }

    if (!this.hasMoreTokens()) {
      return this.onToken(EOF_TOKEN);
    }

    var string = this._string.slice(this._cursor);
    var lexRulesForState = lexRulesByConditions[this.getCurrentState()];

    for (var i = 0; i < lexRulesForState.length; i++) {
      var lexRuleIndex = lexRulesForState[i];
      var lexRule = lexRules[lexRuleIndex];

      var matched = this._match(string, lexRule[0]);

      // Manual handling of EOF token (the end of string). Return it
      // as `EOF` symbol.
      if (string === '' && matched === '') {
        this._cursor++;
      }

      if (matched !== null) {
        yytext = matched;
        yyleng = yytext.length;
        var token = lexRule[1].call(this);

        if (!token) {
          return this.getNextToken();
        }

        // If multiple tokens are returned, save them to return
        // on next `getNextToken` call.

        if (Array.isArray(token)) {
          var tokensToQueue = token.slice(1);
          token = token[0];
          if (tokensToQueue.length > 0) {
            var _tokensQueue;

            (_tokensQueue = this._tokensQueue).unshift.apply(_tokensQueue, _toConsumableArray(tokensToQueue));
          }
        }

        return this.onToken(this._toToken(token, yytext));
      }
    }

    if (this.isEOF()) {
      this._cursor++;
      return EOF_TOKEN;
    }

    this.throwUnexpectedToken(string[0], this._currentLine, this._currentColumn);
  },


  /**
   * Throws default "Unexpected token" exception, showing the actual
   * line from the source, pointing with the ^ marker to the bad token.
   * In addition, shows `line:column` location.
   */
  throwUnexpectedToken: function throwUnexpectedToken(symbol, line, column) {
    var lineSource = this._string.split('\n')[line - 1];
    var lineData = '';

    if (lineSource) {
      var pad = ' '.repeat(column);
      lineData = '\n\n' + lineSource + '\n' + pad + '^\n';
    }

    throw new SyntaxError(lineData + 'Unexpected token: "' + symbol + '" ' + ('at ' + line + ':' + column + '.'));
  },
  getCursor: function getCursor() {
    return this._cursor;
  },
  getCurrentLine: function getCurrentLine() {
    return this._currentLine;
  },
  getCurrentColumn: function getCurrentColumn() {
    return this._currentColumn;
  },
  _captureLocation: function _captureLocation(matched) {
    var nlRe = /\n/g;

    // Absolute offsets.
    this._tokenStartOffset = this._cursor;

    // Line-based locations, start.
    this._tokenStartLine = this._currentLine;
    this._tokenStartColumn = this._tokenStartOffset - this._currentLineBeginOffset;

    // Extract `\n` in the matched token.
    var nlMatch = void 0;
    while ((nlMatch = nlRe.exec(matched)) !== null) {
      this._currentLine++;
      this._currentLineBeginOffset = this._tokenStartOffset + nlMatch.index + 1;
    }

    this._tokenEndOffset = this._cursor + matched.length;

    // Line-based locations, end.
    this._tokenEndLine = this._currentLine;
    this._tokenEndColumn = this._currentColumn = this._tokenEndOffset - this._currentLineBeginOffset;
  },
  _toToken: function _toToken(tokenType) {
    var yytext = arguments.length > 1 && arguments[1] !== undefined ? arguments[1] : '';

    return {
      // Basic data.
      type: tokenType,
      value: yytext,

      // Location data.
      startOffset: this._tokenStartOffset,
      endOffset: this._tokenEndOffset,
      startLine: this._tokenStartLine,
      endLine: this._tokenEndLine,
      startColumn: this._tokenStartColumn,
      endColumn: this._tokenEndColumn
    };
  },
  isEOF: function isEOF() {
    return this._cursor === this._string.length;
  },
  hasMoreTokens: function hasMoreTokens() {
    return this._cursor <= this._string.length;
  },
  _match: function _match(string, regexp) {
    var matched = string.match(regexp);
    if (matched) {
      // Handle `\n` in the matched token to track line numbers.
      this._captureLocation(matched[0]);
      this._cursor += matched[0].length;
      return matched[0];
    }
    return null;
  },


  /**
   * Allows analyzing, and transforming token. Default implementation
   * just passes the token through.
   */
  onToken: function onToken(token) {
    return token;
  }
};

/**
 * Expose tokenizer so it can be accessed in semantic actions.
 */
yy.lexer = tokenizer;
yy.tokenizer = tokenizer;

/**
 * Global parsing options. Some options can be shadowed per
 * each `parse` call, if the optations are passed.
 *
 * Initalized to the `captureLocations` which is passed
 * from the generator. Other options can be added at runtime.
 */
yy.options = {
  captureLocations: true
};

/**
 * Parsing module.
 */
var yyparse = {
  /**
   * Sets global parsing options.
   */
  setOptions: function setOptions(options) {
    yy.options = options;
    return this;
  },


  /**
   * Returns parsing options.
   */
  getOptions: function getOptions() {
    return yy.options;
  },


  /**
   * Parses a string.
   */
  parse: function parse(string, parseOptions) {
    if (!tokenizer) {
      throw new Error('Tokenizer instance wasn\'t specified.');
    }

    tokenizer.initString(string);

    /**
     * If parse options are passed, override global parse options for
     * this call, and later restore global options.
     */
    var globalOptions = yy.options;
    if (parseOptions) {
      yy.options = Object.assign({}, yy.options, parseOptions);
    }

    /**
     * Allow callers to do setup work based on the
     * parsing string, and passed options.
     */
    yyparse.onParseBegin(string, tokenizer, yy.options);

    stack.length = 0;
    stack.push(0);

    var token = tokenizer.getNextToken();
    var shiftedToken = null;

    do {
      if (!token) {
        // Restore options.
        yy.options = globalOptions;
        unexpectedEndOfInput();
      }

      var state = stack[stack.length - 1];
      var column = tokens[token.type];

      if (!table[state].hasOwnProperty(column)) {
        yy.options = globalOptions;
        unexpectedToken(token);
      }

      var entry = table[state][column];

      // Shift action.
      if (entry[0] === 's') {
        var _loc2 = null;

        if (yy.options.captureLocations) {
          _loc2 = {
            startOffset: token.startOffset,
            endOffset: token.endOffset,
            startLine: token.startLine,
            endLine: token.endLine,
            startColumn: token.startColumn,
            endColumn: token.endColumn
          };
        }

        shiftedToken = this.onShift(token);

        stack.push({ symbol: tokens[shiftedToken.type], semanticValue: shiftedToken.value, loc: _loc2 }, Number(entry.slice(1)));

        token = tokenizer.getNextToken();
      }

      // Reduce action.
      else if (entry[0] === 'r') {
          var productionNumber = entry.slice(1);
          var production = productions[productionNumber];
          var hasSemanticAction = typeof production[2] === 'function';
          var semanticValueArgs = hasSemanticAction ? [] : null;

          var locationArgs = hasSemanticAction && yy.options.captureLocations ? [] : null;

          if (production[1] !== 0) {
            var rhsLength = production[1];
            while (rhsLength-- > 0) {
              stack.pop();
              var stackEntry = stack.pop();

              if (hasSemanticAction) {
                semanticValueArgs.unshift(stackEntry.semanticValue);

                if (locationArgs) {
                  locationArgs.unshift(stackEntry.loc);
                }
              }
            }
          }

          var reduceStackEntry = { symbol: production[0] };

          if (hasSemanticAction) {
            yytext = shiftedToken ? shiftedToken.value : null;
            yyleng = shiftedToken ? shiftedToken.value.length : null;

            var semanticActionArgs = locationArgs !== null ? semanticValueArgs.concat(locationArgs) : semanticValueArgs;

            production[2].apply(production, _toConsumableArray(semanticActionArgs));

            reduceStackEntry.semanticValue = __;

            if (locationArgs) {
              reduceStackEntry.loc = __loc;
            }
          }

          var nextState = stack[stack.length - 1];
          var symbolToReduceWith = production[0];

          stack.push(reduceStackEntry, table[nextState][symbolToReduceWith]);
        }

        // Accept.
        else if (entry === 'acc') {
            stack.pop();
            var parsed = stack.pop();

            if (stack.length !== 1 || stack[0] !== 0 || tokenizer.hasMoreTokens()) {
              // Restore options.
              yy.options = globalOptions;
              unexpectedToken(token);
            }

            if (parsed.hasOwnProperty('semanticValue')) {
              yy.options = globalOptions;
              yyparse.onParseEnd(parsed.semanticValue);
              return parsed.semanticValue;
            }

            yyparse.onParseEnd();

            // Restore options.
            yy.options = globalOptions;
            return true;
          }
    } while (tokenizer.hasMoreTokens() || stack.length > 1);
  },
  setTokenizer: function setTokenizer(customTokenizer) {
    tokenizer = customTokenizer;
    return yyparse;
  },
  getTokenizer: function getTokenizer() {
    return tokenizer;
  },
  onParseBegin: function onParseBegin(string, tokenizer, options) {},
  onParseEnd: function onParseEnd(parsed) {},


  /**
   * Allows analyzing, and transforming shifted token. Default implementation
   * just passes the token through.
   */
  onShift: function onShift(token) {
    return token;
  }
};

/**
 * Tracks capturing groups.
 */
var capturingGroupsCount = 0;

/**
 * Tracks named groups.
 */
var namedGroups = {};

/**
 * Parsing string.
 */
var parsingString = '';

yyparse.onParseBegin = function (string, lexer) {
  parsingString = string;
  capturingGroupsCount = 0;
  namedGroups = {};

  var lastSlash = string.lastIndexOf('/');
  var flags = string.slice(lastSlash);

  if (flags.includes('x') && flags.includes('u')) {
    lexer.pushState('xu');
  } else {
    if (flags.includes('x')) {
      lexer.pushState('x');
    }
    if (flags.includes('u')) {
      lexer.pushState('u');
    }
  }
};

/**
 * On shifting `(` remember its number to used on reduce.
 */
yyparse.onShift = function (token) {
  if (token.type === 'L_PAREN' || token.type === 'NAMED_CAPTURE_GROUP') {
    token.value = new String(token.value);
    token.value.groupNumber = ++capturingGroupsCount;
  }
  return token;
};

/**
 * Extracts ranges from the range string.
 */
function getRange(text) {
  var range = text.match(/\d+/g).map(Number);

  if (Number.isFinite(range[1]) && range[1] < range[0]) {
    throw new SyntaxError('Numbers out of order in ' + text + ' quantifier');
  }

  return range;
}

/**
 * Checks class range
 */
function checkClassRange(from, to) {
  if (from.kind === 'control' || to.kind === 'control' || !isNaN(from.codePoint) && !isNaN(to.codePoint) && from.codePoint > to.codePoint) {
    throw new SyntaxError('Range ' + from.value + '-' + to.value + ' out of order in character class');
  }
}

// ---------------------- Unicode property -------------------------------------------

var unicodeProperties = require('../unicode/parser-unicode-properties.js');

/**
 * Unicode property.
 */
function UnicodeProperty(matched, loc) {
  var negative = matched[1] === 'P';
  var separatorIdx = matched.indexOf('=');

  var name = matched.slice(3, separatorIdx !== -1 ? separatorIdx : -1);
  var value = void 0;

  // General_Category allows using only value as a shorthand.
  var isShorthand = separatorIdx === -1 && unicodeProperties.isGeneralCategoryValue(name);

  // Binary propery name.
  var isBinaryProperty = separatorIdx === -1 && unicodeProperties.isBinaryPropertyName(name);

  if (isShorthand) {
    value = name;
    name = 'General_Category';
  } else if (isBinaryProperty) {
    value = name;
  } else {
    if (!unicodeProperties.isValidName(name)) {
      throw new SyntaxError('Invalid unicode property name: ' + name + '.');
    }

    value = matched.slice(separatorIdx + 1, -1);

    if (!unicodeProperties.isValidValue(name, value)) {
      throw new SyntaxError('Invalid ' + name + ' unicode property value: ' + value + '.');
    }
  }

  return Node({
    type: 'UnicodeProperty',
    name: name,
    value: value,
    negative: negative,
    shorthand: isShorthand,
    binary: isBinaryProperty,
    canonicalName: unicodeProperties.getCanonicalName(name) || name,
    canonicalValue: unicodeProperties.getCanonicalValue(value) || value
  }, loc);
}

// ----------------------------------------------------------------------------------


/**
 * Creates a character node.
 */
function Char(value, kind, loc) {
  var symbol = void 0;
  var codePoint = void 0;

  switch (kind) {
    case 'decimal':
      {
        codePoint = Number(value.slice(1));
        symbol = String.fromCodePoint(codePoint);
        break;
      }
    case 'oct':
      {
        codePoint = parseInt(value.slice(1), 8);
        symbol = String.fromCodePoint(codePoint);
        break;
      }
    case 'hex':
    case 'unicode':
      {
        if (value.lastIndexOf('\\u') > 0) {
          var _value$split$slice = value.split('\\u').slice(1),
              _value$split$slice2 = _slicedToArray(_value$split$slice, 2),
              lead = _value$split$slice2[0],
              trail = _value$split$slice2[1];

          lead = parseInt(lead, 16);
          trail = parseInt(trail, 16);
          codePoint = (lead - 0xd800) * 0x400 + (trail - 0xdc00) + 0x10000;

          symbol = String.fromCodePoint(codePoint);
        } else {
          var hex = value.slice(2).replace('{', '');
          codePoint = parseInt(hex, 16);
          if (codePoint > 0x10ffff) {
            throw new SyntaxError('Bad character escape sequence: ' + value);
          }

          symbol = String.fromCodePoint(codePoint);
        }
        break;
      }
    case 'meta':
      {
        switch (value) {
          case '\\t':
            symbol = '\t';
            codePoint = symbol.codePointAt(0);
            break;
          case '\\n':
            symbol = '\n';
            codePoint = symbol.codePointAt(0);
            break;
          case '\\r':
            symbol = '\r';
            codePoint = symbol.codePointAt(0);
            break;
          case '\\v':
            symbol = '\v';
            codePoint = symbol.codePointAt(0);
            break;
          case '\\f':
            symbol = '\f';
            codePoint = symbol.codePointAt(0);
            break;
          case '\\b':
            symbol = '\b';
            codePoint = symbol.codePointAt(0);
          case '\\0':
            symbol = '\0';
            codePoint = 0;
          case '.':
            symbol = '.';
            codePoint = NaN;
            break;
          default:
            codePoint = NaN;
        }
        break;
      }
    case 'simple':
      {
        symbol = value;
        codePoint = symbol.codePointAt(0);
        break;
      }
  }

  return Node({
    type: 'Char',
    value: value,
    kind: kind,
    symbol: symbol,
    codePoint: codePoint
  }, loc);
}

/**
 * Valid flags per current ECMAScript spec and
 * stage 3+ proposals.
 */
var validFlags = 'gimsuxy';

/**
 * Checks the flags are valid, and that
 * we don't duplicate flags.
 */
function checkFlags(flags) {
  var seen = new Set();

  var _iteratorNormalCompletion = true;
  var _didIteratorError = false;
  var _iteratorError = undefined;

  try {
    for (var _iterator = flags[Symbol.iterator](), _step; !(_iteratorNormalCompletion = (_step = _iterator.next()).done); _iteratorNormalCompletion = true) {
      var flag = _step.value;

      if (seen.has(flag) || !validFlags.includes(flag)) {
        throw new SyntaxError('Invalid flags: ' + flags);
      }
      seen.add(flag);
    }
  } catch (err) {
    _didIteratorError = true;
    _iteratorError = err;
  } finally {
    try {
      if (!_iteratorNormalCompletion && _iterator.return) {
        _iterator.return();
      }
    } finally {
      if (_didIteratorError) {
        throw _iteratorError;
      }
    }
  }

  return flags.split('').sort().join('');
}

/**
 * Parses patterns like \1, \2, etc. either as a backreference
 * to a group, or a deciaml char code.
 */
function GroupRefOrDecChar(text, textLoc) {
  var reference = Number(text.slice(1));

  if (reference > 0 && reference <= capturingGroupsCount) {
    return Node({
      type: 'Backreference',
      kind: 'number',
      number: reference,
      reference: reference
    }, textLoc);
  }

  return Char(text, 'decimal', textLoc);
}

/**
 * Unicode names.
 */
var uReStart = /^\\u[0-9a-fA-F]{4}/; // only matches start of string
var ucpReStart = /^\\u\{[0-9a-fA-F]{1,}\}/; // only matches start of string
var ucpReAnywhere = /\\u\{[0-9a-fA-F]{1,}\}/; // matches anywhere in string

/**
 * Validates Unicode group name.
 */
function validateUnicodeGroupName(name, state) {
  var isUnicodeName = ucpReAnywhere.test(name);
  var isUnicodeState = state === 'u' || state === 'xu' || state === 'u_class';

  if (isUnicodeName && !isUnicodeState) {
    throw new SyntaxError('invalid group Unicode name "' + name + '", use `u` flag.');
  }

  return name;
}

// Matches the following production: https://tc39.es/ecma262/#prod-RegExpUnicodeEscapeSequence
//
//  RegExpUnicodeEscapeSequence ::
//    `u` LeadSurrogate `\u` TrailSurrogate   # as 'leadSurrogate', 'trailSurrogate'
//    `u` LeadSurrogate                       # as 'leadSurrogateOnly'
//    `u` TrailSurrogate                      # as 'trailSurrogateOnly'
//    `u` NonSurrogate                        # as 'nonSurrogate'
//    `u` `{` CodePoint `}`                   # as 'codePoint'
//
//  LeadSurrogate ::
//    Hex4Digits but only if the SV of Hex4Digits is in the inclusive range 0xD800 to 0xDBFF        # [dD][89aAbB][0-9a-fA-F]{2}
//
//  TrailSurrogate ::
//    Hex4Digits but only if the SV of Hex4Digits is in the inclusive range 0xDC00 to 0xDFFF        # [dD][c-fC-F][0-9a-fA-F]{2}
//
//  NonSurrogate ::
//    Hex4Digits but only if the SV of Hex4Digits is not in the inclusive range 0xD800 to 0xDFFF    # [0-9a-ce-fA-CE-F][0-9a-fA-F]{3}|[dD][0-7][0-9a-fA-F]{2}
//
//  CodePoint ::
//    HexDigits but only if MV of HexDigits ≤ 0x10FFFF                                              # 0*(?:[0-9a-fA-F]{1,5}|10[0-9a-fA-F]{4})
//
var uidRe = /\\u(?:([dD][89aAbB][0-9a-fA-F]{2})\\u([dD][c-fC-F][0-9a-fA-F]{2})|([dD][89aAbB][0-9a-fA-F]{2})|([dD][c-fC-F][0-9a-fA-F]{2})|([0-9a-ce-fA-CE-F][0-9a-fA-F]{3}|[dD][0-7][0-9a-fA-F]{2})|\{(0*(?:[0-9a-fA-F]{1,5}|10[0-9a-fA-F]{4}))\})/;

function decodeUnicodeGroupName(name) {
  return name.replace(new RegExp(uidRe, 'g'), function (_, leadSurrogate, trailSurrogate, leadSurrogateOnly, trailSurrogateOnly, nonSurrogate, codePoint) {
    if (leadSurrogate) {
      return String.fromCodePoint(parseInt(leadSurrogate, 16), parseInt(trailSurrogate, 16));
    }
    if (leadSurrogateOnly) {
      return String.fromCodePoint(parseInt(leadSurrogateOnly, 16));
    }
    if (trailSurrogateOnly) {
      // TODO: Per the spec: https://tc39.es/ecma262/#prod-RegExpUnicodeEscapeSequence
      // > Each `\u` TrailSurrogate for which the choice of associated `u` LeadSurrogate is ambiguous shall be associated with the nearest possible `u` LeadSurrogate that would otherwise have no corresponding `\u` TrailSurrogate.
      return String.fromCodePoint(parseInt(trailSurrogateOnly, 16));
    }
    if (nonSurrogate) {
      return String.fromCodePoint(parseInt(nonSurrogate, 16));
    }
    if (codePoint) {
      return String.fromCodePoint(parseInt(codePoint, 16));
    }
    return _;
  });
}

/**
 * Extracts from `\k<foo>` pattern either a backreference
 * to a named capturing group (if it presents), or parses it
 * as a list of char: `\k`, `<`, `f`, etc.
 */
function NamedGroupRefOrChars(text, textLoc) {
  var referenceRaw = text.slice(3, -1);
  var reference = decodeUnicodeGroupName(referenceRaw);

  if (namedGroups.hasOwnProperty(reference)) {
    return Node({
      type: 'Backreference',
      kind: 'name',
      number: namedGroups[reference],
      reference: reference,
      referenceRaw: referenceRaw
    }, textLoc);
  }

  // Else `\k<foo>` should be parsed as a list of `Char`s.
  // This is really a 0.01% edge case, but we should handle it.

  var startOffset = null;
  var startLine = null;
  var endLine = null;
  var startColumn = null;

  if (textLoc) {
    startOffset = textLoc.startOffset;
    startLine = textLoc.startLine;
    endLine = textLoc.endLine;
    startColumn = textLoc.startColumn;
  }

  var charRe = /^[\w$<>]/;
  var loc = void 0;

  var chars = [
  // Init to first \k, taking 2 symbols.
  Char(text.slice(1, 2), 'simple', startOffset ? {
    startLine: startLine,
    endLine: endLine,
    startColumn: startColumn,
    startOffset: startOffset,
    endOffset: startOffset += 2,
    endColumn: startColumn += 2
  } : null)];

  // For \k
  chars[0].escaped = true;

  // Other symbols.
  text = text.slice(2);

  while (text.length > 0) {
    var matched = null;

    // Unicode, \u003B or \u{003B}
    if ((matched = text.match(uReStart)) || (matched = text.match(ucpReStart))) {
      if (startOffset) {
        loc = {
          startLine: startLine,
          endLine: endLine,
          startColumn: startColumn,
          startOffset: startOffset,
          endOffset: startOffset += matched[0].length,
          endColumn: startColumn += matched[0].length
        };
      }
      chars.push(Char(matched[0], 'unicode', loc));
      text = text.slice(matched[0].length);
    }

    // Simple char.
    else if (matched = text.match(charRe)) {
        if (startOffset) {
          loc = {
            startLine: startLine,
            endLine: endLine,
            startColumn: startColumn,
            startOffset: startOffset,
            endOffset: ++startOffset,
            endColumn: ++startColumn
          };
        }
        chars.push(Char(matched[0], 'simple', loc));
        text = text.slice(1);
      }
  }

  return chars;
}

/**
 * Creates an AST node with a location.
 */
function Node(node, loc) {
  if (yy.options.captureLocations) {
    node.loc = {
      source: parsingString.slice(loc.startOffset, loc.endOffset),
      start: {
        line: loc.startLine,
        column: loc.startColumn,
        offset: loc.startOffset
      },
      end: {
        line: loc.endLine,
        column: loc.endColumn,
        offset: loc.endOffset
      }
    };
  }
  return node;
}

/**
 * Creates location node.
 */
function loc(start, end) {
  if (!yy.options.captureLocations) {
    return null;
  }

  return {
    startOffset: start.startOffset,
    endOffset: end.endOffset,
    startLine: start.startLine,
    endLine: end.endLine,
    startColumn: start.startColumn,
    endColumn: end.endColumn
  };
}

function unexpectedToken(token) {
  if (token.type === EOF) {
    unexpectedEndOfInput();
  }

  tokenizer.throwUnexpectedToken(token.value, token.startLine, token.startColumn);
}

function unexpectedEndOfInput() {
  parseError('Unexpected end of input.');
}

function parseError(message) {
  throw new SyntaxError(message);
}

module.exports = yyparse;
},{"../unicode/parser-unicode-properties.js":47}],46:[function(require,module,exports){
/**
 * The MIT License (MIT)
 * Copyright (c) 2017-present Dmitry Soshnikov <dmitry.soshnikov@gmail.com>
 */

'use strict';

var regexpTreeParser = require('./generated/regexp-tree');

/**
 * Original parse function.
 */
var generatedParseFn = regexpTreeParser.parse.bind(regexpTreeParser);

/**
 * Parses a regular expression.
 *
 * Override original `regexpTreeParser.parse` to convert a value to a string,
 * since in regexp-tree we may pass strings, and RegExp instance.
 */
regexpTreeParser.parse = function (regexp, options) {
  return generatedParseFn('' + regexp, options);
};

// By default do not capture locations; callers may override.
regexpTreeParser.setOptions({ captureLocations: false });

module.exports = regexpTreeParser;
},{"./generated/regexp-tree":45}],47:[function(require,module,exports){
'use strict';

/**
 * The MIT License (MIT)
 * Copyright (c) 2017-present Dmitry Soshnikov <dmitry.soshnikov@gmail.com>
 */

var NON_BINARY_PROP_NAMES_TO_ALIASES = {
  General_Category: 'gc',
  Script: 'sc',
  Script_Extensions: 'scx'
};

var NON_BINARY_ALIASES_TO_PROP_NAMES = inverseMap(NON_BINARY_PROP_NAMES_TO_ALIASES);

var BINARY_PROP_NAMES_TO_ALIASES = {
  ASCII: 'ASCII',
  ASCII_Hex_Digit: 'AHex',
  Alphabetic: 'Alpha',
  Any: 'Any',
  Assigned: 'Assigned',
  Bidi_Control: 'Bidi_C',
  Bidi_Mirrored: 'Bidi_M',
  Case_Ignorable: 'CI',
  Cased: 'Cased',
  Changes_When_Casefolded: 'CWCF',
  Changes_When_Casemapped: 'CWCM',
  Changes_When_Lowercased: 'CWL',
  Changes_When_NFKC_Casefolded: 'CWKCF',
  Changes_When_Titlecased: 'CWT',
  Changes_When_Uppercased: 'CWU',
  Dash: 'Dash',
  Default_Ignorable_Code_Point: 'DI',
  Deprecated: 'Dep',
  Diacritic: 'Dia',
  Emoji: 'Emoji',
  Emoji_Component: 'Emoji_Component',
  Emoji_Modifier: 'Emoji_Modifier',
  Emoji_Modifier_Base: 'Emoji_Modifier_Base',
  Emoji_Presentation: 'Emoji_Presentation',
  Extended_Pictographic: 'Extended_Pictographic',
  Extender: 'Ext',
  Grapheme_Base: 'Gr_Base',
  Grapheme_Extend: 'Gr_Ext',
  Hex_Digit: 'Hex',
  IDS_Binary_Operator: 'IDSB',
  IDS_Trinary_Operator: 'IDST',
  ID_Continue: 'IDC',
  ID_Start: 'IDS',
  Ideographic: 'Ideo',
  Join_Control: 'Join_C',
  Logical_Order_Exception: 'LOE',
  Lowercase: 'Lower',
  Math: 'Math',
  Noncharacter_Code_Point: 'NChar',
  Pattern_Syntax: 'Pat_Syn',
  Pattern_White_Space: 'Pat_WS',
  Quotation_Mark: 'QMark',
  Radical: 'Radical',
  Regional_Indicator: 'RI',
  Sentence_Terminal: 'STerm',
  Soft_Dotted: 'SD',
  Terminal_Punctuation: 'Term',
  Unified_Ideograph: 'UIdeo',
  Uppercase: 'Upper',
  Variation_Selector: 'VS',
  White_Space: 'space',
  XID_Continue: 'XIDC',
  XID_Start: 'XIDS'
};

var BINARY_ALIASES_TO_PROP_NAMES = inverseMap(BINARY_PROP_NAMES_TO_ALIASES);

var GENERAL_CATEGORY_VALUE_TO_ALIASES = {
  Cased_Letter: 'LC',
  Close_Punctuation: 'Pe',
  Connector_Punctuation: 'Pc',
  Control: ['Cc', 'cntrl'],
  Currency_Symbol: 'Sc',
  Dash_Punctuation: 'Pd',
  Decimal_Number: ['Nd', 'digit'],
  Enclosing_Mark: 'Me',
  Final_Punctuation: 'Pf',
  Format: 'Cf',
  Initial_Punctuation: 'Pi',
  Letter: 'L',
  Letter_Number: 'Nl',
  Line_Separator: 'Zl',
  Lowercase_Letter: 'Ll',
  Mark: ['M', 'Combining_Mark'],
  Math_Symbol: 'Sm',
  Modifier_Letter: 'Lm',
  Modifier_Symbol: 'Sk',
  Nonspacing_Mark: 'Mn',
  Number: 'N',
  Open_Punctuation: 'Ps',
  Other: 'C',
  Other_Letter: 'Lo',
  Other_Number: 'No',
  Other_Punctuation: 'Po',
  Other_Symbol: 'So',
  Paragraph_Separator: 'Zp',
  Private_Use: 'Co',
  Punctuation: ['P', 'punct'],
  Separator: 'Z',
  Space_Separator: 'Zs',
  Spacing_Mark: 'Mc',
  Surrogate: 'Cs',
  Symbol: 'S',
  Titlecase_Letter: 'Lt',
  Unassigned: 'Cn',
  Uppercase_Letter: 'Lu'
};

var GENERAL_CATEGORY_VALUE_ALIASES_TO_VALUES = inverseMap(GENERAL_CATEGORY_VALUE_TO_ALIASES);

var SCRIPT_VALUE_TO_ALIASES = {
  Adlam: 'Adlm',
  Ahom: 'Ahom',
  Anatolian_Hieroglyphs: 'Hluw',
  Arabic: 'Arab',
  Armenian: 'Armn',
  Avestan: 'Avst',
  Balinese: 'Bali',
  Bamum: 'Bamu',
  Bassa_Vah: 'Bass',
  Batak: 'Batk',
  Bengali: 'Beng',
  Bhaiksuki: 'Bhks',
  Bopomofo: 'Bopo',
  Brahmi: 'Brah',
  Braille: 'Brai',
  Buginese: 'Bugi',
  Buhid: 'Buhd',
  Canadian_Aboriginal: 'Cans',
  Carian: 'Cari',
  Caucasian_Albanian: 'Aghb',
  Chakma: 'Cakm',
  Cham: 'Cham',
  Cherokee: 'Cher',
  Common: 'Zyyy',
  Coptic: ['Copt', 'Qaac'],
  Cuneiform: 'Xsux',
  Cypriot: 'Cprt',
  Cyrillic: 'Cyrl',
  Deseret: 'Dsrt',
  Devanagari: 'Deva',
  Dogra: 'Dogr',
  Duployan: 'Dupl',
  Egyptian_Hieroglyphs: 'Egyp',
  Elbasan: 'Elba',
  Ethiopic: 'Ethi',
  Georgian: 'Geor',
  Glagolitic: 'Glag',
  Gothic: 'Goth',
  Grantha: 'Gran',
  Greek: 'Grek',
  Gujarati: 'Gujr',
  Gunjala_Gondi: 'Gong',
  Gurmukhi: 'Guru',
  Han: 'Hani',
  Hangul: 'Hang',
  Hanifi_Rohingya: 'Rohg',
  Hanunoo: 'Hano',
  Hatran: 'Hatr',
  Hebrew: 'Hebr',
  Hiragana: 'Hira',
  Imperial_Aramaic: 'Armi',
  Inherited: ['Zinh', 'Qaai'],
  Inscriptional_Pahlavi: 'Phli',
  Inscriptional_Parthian: 'Prti',
  Javanese: 'Java',
  Kaithi: 'Kthi',
  Kannada: 'Knda',
  Katakana: 'Kana',
  Kayah_Li: 'Kali',
  Kharoshthi: 'Khar',
  Khmer: 'Khmr',
  Khojki: 'Khoj',
  Khudawadi: 'Sind',
  Lao: 'Laoo',
  Latin: 'Latn',
  Lepcha: 'Lepc',
  Limbu: 'Limb',
  Linear_A: 'Lina',
  Linear_B: 'Linb',
  Lisu: 'Lisu',
  Lycian: 'Lyci',
  Lydian: 'Lydi',
  Mahajani: 'Mahj',
  Makasar: 'Maka',
  Malayalam: 'Mlym',
  Mandaic: 'Mand',
  Manichaean: 'Mani',
  Marchen: 'Marc',
  Medefaidrin: 'Medf',
  Masaram_Gondi: 'Gonm',
  Meetei_Mayek: 'Mtei',
  Mende_Kikakui: 'Mend',
  Meroitic_Cursive: 'Merc',
  Meroitic_Hieroglyphs: 'Mero',
  Miao: 'Plrd',
  Modi: 'Modi',
  Mongolian: 'Mong',
  Mro: 'Mroo',
  Multani: 'Mult',
  Myanmar: 'Mymr',
  Nabataean: 'Nbat',
  New_Tai_Lue: 'Talu',
  Newa: 'Newa',
  Nko: 'Nkoo',
  Nushu: 'Nshu',
  Ogham: 'Ogam',
  Ol_Chiki: 'Olck',
  Old_Hungarian: 'Hung',
  Old_Italic: 'Ital',
  Old_North_Arabian: 'Narb',
  Old_Permic: 'Perm',
  Old_Persian: 'Xpeo',
  Old_Sogdian: 'Sogo',
  Old_South_Arabian: 'Sarb',
  Old_Turkic: 'Orkh',
  Oriya: 'Orya',
  Osage: 'Osge',
  Osmanya: 'Osma',
  Pahawh_Hmong: 'Hmng',
  Palmyrene: 'Palm',
  Pau_Cin_Hau: 'Pauc',
  Phags_Pa: 'Phag',
  Phoenician: 'Phnx',
  Psalter_Pahlavi: 'Phlp',
  Rejang: 'Rjng',
  Runic: 'Runr',
  Samaritan: 'Samr',
  Saurashtra: 'Saur',
  Sharada: 'Shrd',
  Shavian: 'Shaw',
  Siddham: 'Sidd',
  SignWriting: 'Sgnw',
  Sinhala: 'Sinh',
  Sogdian: 'Sogd',
  Sora_Sompeng: 'Sora',
  Soyombo: 'Soyo',
  Sundanese: 'Sund',
  Syloti_Nagri: 'Sylo',
  Syriac: 'Syrc',
  Tagalog: 'Tglg',
  Tagbanwa: 'Tagb',
  Tai_Le: 'Tale',
  Tai_Tham: 'Lana',
  Tai_Viet: 'Tavt',
  Takri: 'Takr',
  Tamil: 'Taml',
  Tangut: 'Tang',
  Telugu: 'Telu',
  Thaana: 'Thaa',
  Thai: 'Thai',
  Tibetan: 'Tibt',
  Tifinagh: 'Tfng',
  Tirhuta: 'Tirh',
  Ugaritic: 'Ugar',
  Vai: 'Vaii',
  Warang_Citi: 'Wara',
  Yi: 'Yiii',
  Zanabazar_Square: 'Zanb'
};

var SCRIPT_VALUE_ALIASES_TO_VALUE = inverseMap(SCRIPT_VALUE_TO_ALIASES);

function inverseMap(data) {
  var inverse = {};

  for (var name in data) {
    if (!data.hasOwnProperty(name)) {
      continue;
    }
    var value = data[name];
    if (Array.isArray(value)) {
      for (var i = 0; i < value.length; i++) {
        inverse[value[i]] = name;
      }
    } else {
      inverse[value] = name;
    }
  }

  return inverse;
}

function isValidName(name) {
  return NON_BINARY_PROP_NAMES_TO_ALIASES.hasOwnProperty(name) || NON_BINARY_ALIASES_TO_PROP_NAMES.hasOwnProperty(name) || BINARY_PROP_NAMES_TO_ALIASES.hasOwnProperty(name) || BINARY_ALIASES_TO_PROP_NAMES.hasOwnProperty(name);
}

function isValidValue(name, value) {
  if (isGeneralCategoryName(name)) {
    return isGeneralCategoryValue(value);
  }

  if (isScriptCategoryName(name)) {
    return isScriptCategoryValue(value);
  }

  return false;
}

function isAlias(name) {
  return NON_BINARY_ALIASES_TO_PROP_NAMES.hasOwnProperty(name) || BINARY_ALIASES_TO_PROP_NAMES.hasOwnProperty(name);
}

function isGeneralCategoryName(name) {
  return name === 'General_Category' || name == 'gc';
}

function isScriptCategoryName(name) {
  return name === 'Script' || name === 'Script_Extensions' || name === 'sc' || name === 'scx';
}

function isGeneralCategoryValue(value) {
  return GENERAL_CATEGORY_VALUE_TO_ALIASES.hasOwnProperty(value) || GENERAL_CATEGORY_VALUE_ALIASES_TO_VALUES.hasOwnProperty(value);
}

function isScriptCategoryValue(value) {
  return SCRIPT_VALUE_TO_ALIASES.hasOwnProperty(value) || SCRIPT_VALUE_ALIASES_TO_VALUE.hasOwnProperty(value);
}

function isBinaryPropertyName(name) {
  return BINARY_PROP_NAMES_TO_ALIASES.hasOwnProperty(name) || BINARY_ALIASES_TO_PROP_NAMES.hasOwnProperty(name);
}

function getCanonicalName(name) {
  if (NON_BINARY_ALIASES_TO_PROP_NAMES.hasOwnProperty(name)) {
    return NON_BINARY_ALIASES_TO_PROP_NAMES[name];
  }

  if (BINARY_ALIASES_TO_PROP_NAMES.hasOwnProperty(name)) {
    return BINARY_ALIASES_TO_PROP_NAMES[name];
  }

  return null;
}

function getCanonicalValue(value) {
  if (GENERAL_CATEGORY_VALUE_ALIASES_TO_VALUES.hasOwnProperty(value)) {
    return GENERAL_CATEGORY_VALUE_ALIASES_TO_VALUES[value];
  }

  if (SCRIPT_VALUE_ALIASES_TO_VALUE.hasOwnProperty(value)) {
    return SCRIPT_VALUE_ALIASES_TO_VALUE[value];
  }

  if (BINARY_ALIASES_TO_PROP_NAMES.hasOwnProperty(value)) {
    return BINARY_ALIASES_TO_PROP_NAMES[value];
  }

  return null;
}

module.exports = {
  isAlias: isAlias,
  isValidName: isValidName,
  isValidValue: isValidValue,
  isGeneralCategoryValue: isGeneralCategoryValue,
  isScriptCategoryValue: isScriptCategoryValue,
  isBinaryPropertyName: isBinaryPropertyName,
  getCanonicalName: getCanonicalName,
  getCanonicalValue: getCanonicalValue,

  NON_BINARY_PROP_NAMES_TO_ALIASES: NON_BINARY_PROP_NAMES_TO_ALIASES,
  NON_BINARY_ALIASES_TO_PROP_NAMES: NON_BINARY_ALIASES_TO_PROP_NAMES,

  BINARY_PROP_NAMES_TO_ALIASES: BINARY_PROP_NAMES_TO_ALIASES,
  BINARY_ALIASES_TO_PROP_NAMES: BINARY_ALIASES_TO_PROP_NAMES,

  GENERAL_CATEGORY_VALUE_TO_ALIASES: GENERAL_CATEGORY_VALUE_TO_ALIASES,
  GENERAL_CATEGORY_VALUE_ALIASES_TO_VALUES: GENERAL_CATEGORY_VALUE_ALIASES_TO_VALUES,

  SCRIPT_VALUE_TO_ALIASES: SCRIPT_VALUE_TO_ALIASES,
  SCRIPT_VALUE_ALIASES_TO_VALUE: SCRIPT_VALUE_ALIASES_TO_VALUE
};
},{}],48:[function(require,module,exports){
/**
 * The MIT License (MIT)
 * Copyright (c) 2017-present Dmitry Soshnikov <dmitry.soshnikov@gmail.com>
 */

'use strict';

var compatTranspiler = require('./compat-transpiler');
var generator = require('./generator');
var optimizer = require('./optimizer');
var parser = require('./parser');
var _transform = require('./transform');
var _traverse = require('./traverse');
var fa = require('./interpreter/finite-automaton');

var _require = require('./compat-transpiler/runtime'),
    RegExpTree = _require.RegExpTree;

/**
 * An API object for RegExp processing (parsing/transform/generation).
 */


var regexpTree = {
  /**
   * Parser module exposed.
   */
  parser: parser,

  /**
   * Expose finite-automaton module.
   */
  fa: fa,

  /**
   * `TransformResult` exposed.
   */
  TransformResult: _transform.TransformResult,

  /**
   * Parses a regexp string, producing an AST.
   *
   * @param string regexp
   *
   *   a regular expression in different formats: string, AST, RegExp.
   *
   * @param Object options
   *
   *   parsing options for this parse call. Default are:
   *
   *     - captureLocations: boolean
   *     - any other custom options
   *
   * @return Object AST
   */
  parse: function parse(regexp, options) {
    return parser.parse('' + regexp, options);
  },


  /**
   * Traverses a RegExp AST.
   *
   * @param Object ast
   * @param Object | Array<Object> handlers
   *
   * Each `handler` is an object containing handler function for needed
   * node types. Example:
   *
   *   regexpTree.traverse(ast, {
   *     onChar(node) {
   *       ...
   *     },
   *   });
   *
   * The value for a node type may also be an object with functions pre and post.
   * This enables more context-aware analyses, e.g. measuring star height.
   */
  traverse: function traverse(ast, handlers, options) {
    return _traverse.traverse(ast, handlers, options);
  },


  /**
   * Transforms a regular expression.
   *
   * A regexp can be passed in different formats (string, regexp or AST),
   * applying a set of transformations. It is a convenient wrapper
   * on top of "parse-traverse-generate" tool chain.
   *
   * @param string | AST | RegExp regexp - a regular expression;
   * @param Object | Array<Object> handlers - a list of handlers.
   *
   * @return TransformResult - a transformation result.
   */
  transform: function transform(regexp, handlers) {
    return _transform.transform(regexp, handlers);
  },


  /**
   * Generates a RegExp string from an AST.
   *
   * @param Object ast
   *
   * Invariant:
   *
   *   regexpTree.generate(regexpTree.parse('/[a-z]+/i')); // '/[a-z]+/i'
   */
  generate: function generate(ast) {
    return generator.generate(ast);
  },


  /**
   * Creates a RegExp object from a regexp string.
   *
   * @param string regexp
   */
  toRegExp: function toRegExp(regexp) {
    var compat = this.compatTranspile(regexp);
    return new RegExp(compat.getSource(), compat.getFlags());
  },


  /**
   * Optimizes a regular expression by replacing some
   * sub-expressions with their idiomatic patterns.
   *
   * @param string regexp
   *
   * @return TransformResult object
   */
  optimize: function optimize(regexp, whitelist) {
    var _ref = arguments.length > 2 && arguments[2] !== undefined ? arguments[2] : {},
        blacklist = _ref.blacklist;

    return optimizer.optimize(regexp, { whitelist: whitelist, blacklist: blacklist });
  },


  /**
   * Translates a regular expression in new syntax or in new format
   * into equivalent expressions in old syntax.
   *
   * @param string regexp
   *
   * @return TransformResult object
   */
  compatTranspile: function compatTranspile(regexp, whitelist) {
    return compatTranspiler.transform(regexp, whitelist);
  },


  /**
   * Executes a regular expression on a string.
   *
   * @param RegExp|string re - a regular expression.
   * @param string string - a testing string.
   */
  exec: function exec(re, string) {
    if (typeof re === 'string') {
      var compat = this.compatTranspile(re);
      var extra = compat.getExtra();

      if (extra.namedCapturingGroups) {
        re = new RegExpTree(compat.toRegExp(), {
          flags: compat.getFlags(),
          source: compat.getSource(),
          groups: extra.namedCapturingGroups
        });
      } else {
        re = compat.toRegExp();
      }
    }

    return re.exec(string);
  }
};

module.exports = regexpTree;
},{"./compat-transpiler":11,"./compat-transpiler/runtime":12,"./generator":17,"./interpreter/finite-automaton":20,"./optimizer":27,"./parser":46,"./transform":49,"./traverse":51}],49:[function(require,module,exports){
/**
 * The MIT License (MIT)
 * Copyright (c) 2017-present Dmitry Soshnikov <dmitry.soshnikov@gmail.com>
 */

'use strict';

var _createClass = function () { function defineProperties(target, props) { for (var i = 0; i < props.length; i++) { var descriptor = props[i]; descriptor.enumerable = descriptor.enumerable || false; descriptor.configurable = true; if ("value" in descriptor) descriptor.writable = true; Object.defineProperty(target, descriptor.key, descriptor); } } return function (Constructor, protoProps, staticProps) { if (protoProps) defineProperties(Constructor.prototype, protoProps); if (staticProps) defineProperties(Constructor, staticProps); return Constructor; }; }();

function _classCallCheck(instance, Constructor) { if (!(instance instanceof Constructor)) { throw new TypeError("Cannot call a class as a function"); } }

var generator = require('../generator');
var parser = require('../parser');
var traverse = require('../traverse');

/**
 * Transform result.
 */

var TransformResult = function () {
  /**
   * Initializes a transform result for an AST.
   *
   * @param Object ast - an AST node
   * @param mixed extra - any extra data a transform may return
   */
  function TransformResult(ast) {
    var extra = arguments.length > 1 && arguments[1] !== undefined ? arguments[1] : null;

    _classCallCheck(this, TransformResult);

    this._ast = ast;
    this._source = null;
    this._string = null;
    this._regexp = null;
    this._extra = extra;
  }

  _createClass(TransformResult, [{
    key: 'getAST',
    value: function getAST() {
      return this._ast;
    }
  }, {
    key: 'setExtra',
    value: function setExtra(extra) {
      this._extra = extra;
    }
  }, {
    key: 'getExtra',
    value: function getExtra() {
      return this._extra;
    }
  }, {
    key: 'toRegExp',
    value: function toRegExp() {
      if (!this._regexp) {
        this._regexp = new RegExp(this.getSource(), this._ast.flags);
      }
      return this._regexp;
    }
  }, {
    key: 'getSource',
    value: function getSource() {
      if (!this._source) {
        this._source = generator.generate(this._ast.body);
      }
      return this._source;
    }
  }, {
    key: 'getFlags',
    value: function getFlags() {
      return this._ast.flags;
    }
  }, {
    key: 'toString',
    value: function toString() {
      if (!this._string) {
        this._string = generator.generate(this._ast);
      }
      return this._string;
    }
  }]);

  return TransformResult;
}();

module.exports = {
  /**
   * Expose `TransformResult`.
   */
  TransformResult: TransformResult,

  /**
   * Transforms a regular expression applying a set of
   * transformation handlers.
   *
   * @param string | AST | RegExp:
   *
   *   a regular expression in different representations: a string,
   *   a RegExp object, or an AST.
   *
   * @param Object | Array<Object>:
   *
   *   a handler (or a list of handlers) from `traverse` API.
   *
   * @return TransformResult instance.
   *
   * Example:
   *
   *   transform(/[a-z]/i, {
   *     onChar(path) {
   *       const {node} = path;
   *
   *       if (...) {
   *         path.remove();
   *       }
   *     }
   *   });
   */
  transform: function transform(regexp, handlers) {
    var ast = regexp;

    if (regexp instanceof RegExp) {
      regexp = '' + regexp;
    }

    if (typeof regexp === 'string') {
      ast = parser.parse(regexp, {
        captureLocations: true
      });
    }

    traverse.traverse(ast, handlers);

    return new TransformResult(ast);
  }
};
},{"../generator":17,"../parser":46,"../traverse":51}],50:[function(require,module,exports){
/**
 * The MIT License (MIT)
 * Copyright (c) 2017-present Dmitry Soshnikov <dmitry.soshnikov@gmail.com>
 */

'use strict';

/**
 * Flattens a nested disjunction node to a list.
 *
 * /a|b|c|d/
 *
 * {{{a, b}, c}, d} -> [a, b, c, d]
 */

function _toConsumableArray(arr) { if (Array.isArray(arr)) { for (var i = 0, arr2 = Array(arr.length); i < arr.length; i++) { arr2[i] = arr[i]; } return arr2; } else { return Array.from(arr); } }

function disjunctionToList(node) {
  if (node.type !== 'Disjunction') {
    throw new TypeError('Expected "Disjunction" node, got "' + node.type + '"');
  }

  var list = [];

  if (node.left && node.left.type === 'Disjunction') {
    list.push.apply(list, _toConsumableArray(disjunctionToList(node.left)).concat([node.right]));
  } else {
    list.push(node.left, node.right);
  }

  return list;
}

/**
 * Builds a nested disjunction node from a list.
 *
 * /a|b|c|d/
 *
 * [a, b, c, d] -> {{{a, b}, c}, d}
 */
function listToDisjunction(list) {
  return list.reduce(function (left, right) {
    return {
      type: 'Disjunction',
      left: left,
      right: right
    };
  });
}

/**
 * Increases a quantifier by one.
 * Does not change greediness.
 * * -> +
 * + -> {2,}
 * ? -> {1,2}
 * {2} -> {3}
 * {2,} -> {3,}
 * {2,3} -> {3,4}
 */
function increaseQuantifierByOne(quantifier) {
  if (quantifier.kind === '*') {

    quantifier.kind = '+';
  } else if (quantifier.kind === '+') {

    quantifier.kind = 'Range';
    quantifier.from = 2;
    delete quantifier.to;
  } else if (quantifier.kind === '?') {

    quantifier.kind = 'Range';
    quantifier.from = 1;
    quantifier.to = 2;
  } else if (quantifier.kind === 'Range') {

    quantifier.from += 1;
    if (quantifier.to) {
      quantifier.to += 1;
    }
  }
}

module.exports = {
  disjunctionToList: disjunctionToList,
  listToDisjunction: listToDisjunction,
  increaseQuantifierByOne: increaseQuantifierByOne
};
},{}],51:[function(require,module,exports){
/**
 * The MIT License (MIT)
 * Copyright (c) 2017-present Dmitry Soshnikov <dmitry.soshnikov@gmail.com>
 */

'use strict';

var NodePath = require('./node-path');

/**
 * Does an actual AST traversal, using visitor pattern,
 * and calling set of callbacks.
 *
 * Based on https://github.com/olov/ast-traverse
 *
 * Expects AST in Mozilla Parser API: nodes which are supposed to be
 * handled should have `type` property.
 *
 * @param Object root - a root node to start traversal from.
 *
 * @param Object options - an object with set of callbacks:
 *
 *   - `pre(node, parent, prop, index)` - a hook called on node enter
 *   - `post`(node, parent, prop, index) - a hook called on node exit
 *   - `skipProperty(prop)` - a predicated whether a property should be skipped
 */
function astTraverse(root) {
  var options = arguments.length > 1 && arguments[1] !== undefined ? arguments[1] : {};

  var pre = options.pre;
  var post = options.post;
  var skipProperty = options.skipProperty;

  function visit(node, parent, prop, idx) {
    if (!node || typeof node.type !== 'string') {
      return;
    }

    var res = undefined;
    if (pre) {
      res = pre(node, parent, prop, idx);
    }

    if (res !== false) {

      // A node can be replaced during traversal, so we have to
      // recalculate it from the parent, to avoid traversing "dead" nodes.
      if (parent && parent[prop]) {
        if (!isNaN(idx)) {
          node = parent[prop][idx];
        } else {
          node = parent[prop];
        }
      }

      for (var _prop in node) {
        if (node.hasOwnProperty(_prop)) {
          if (skipProperty ? skipProperty(_prop, node) : _prop[0] === '$') {
            continue;
          }

          var child = node[_prop];

          // Collection node.
          //
          // NOTE: a node (or several nodes) can be removed or inserted
          // during traversal.
          //
          // Current traversing index is stored on top of the
          // `NodePath.traversingIndexStack`. The stack is used to support
          // recursive nature of the traversal.
          //
          // In this case `NodePath.traversingIndex` (which we use here) is
          // updated in the NodePath remove/insert methods.
          //
          if (Array.isArray(child)) {
            var index = 0;
            NodePath.traversingIndexStack.push(index);
            while (index < child.length) {
              visit(child[index], node, _prop, index);
              index = NodePath.updateTraversingIndex(+1);
            }
            NodePath.traversingIndexStack.pop();
          }

          // Simple node.
          else {
              visit(child, node, _prop);
            }
        }
      }
    }

    if (post) {
      post(node, parent, prop, idx);
    }
  }

  visit(root, null);
}

module.exports = {
  /**
   * Traverses an AST.
   *
   * @param Object ast - an AST node
   *
   * @param Object | Array<Object> handlers:
   *
   *   an object (or an array of objects)
   *
   *   Each such object contains a handler function per node.
   *   In case of an array of handlers, they are applied in order.
   *   A handler may return a transformed node (or a different type).
   *
   *   The per-node function may instead be an object with functions pre and post.
   *   pre is called before visiting the node, post after.
   *   If a handler is a function, it is treated as the pre function, with an empty post.
   *
   * @param Object options:
   *
   *   a config object, specifying traversal options:
   *
   *   `asNodes`: boolean - whether handlers should receives raw AST nodes
   *   (false by default), instead of a `NodePath` wrapper. Note, by default
   *   `NodePath` wrapper provides a set of convenient method to manipulate
   *   a traversing AST, and also has access to all parents list. A raw
   *   nodes traversal should be used in rare cases, when no `NodePath`
   *   features are needed.
   *
   * Special hooks:
   *
   *   - `shouldRun(ast)` - a predicate determining whether the handler
   *                        should be applied.
   *
   * NOTE: Multiple handlers are used as an optimization of applying all of
   * them in one AST traversal pass.
   */
  traverse: function traverse(ast, handlers) {
    var options = arguments.length > 2 && arguments[2] !== undefined ? arguments[2] : { asNodes: false };


    if (!Array.isArray(handlers)) {
      handlers = [handlers];
    }

    // Filter out handlers by result of `shouldRun`, if the method is present.
    handlers = handlers.filter(function (handler) {
      if (typeof handler.shouldRun !== 'function') {
        return true;
      }
      return handler.shouldRun(ast);
    });

    NodePath.initRegistry();

    // Allow handlers to initializer themselves.
    handlers.forEach(function (handler) {
      if (typeof handler.init === 'function') {
        handler.init(ast);
      }
    });

    function getPathFor(node, parent, prop, index) {
      var parentPath = NodePath.getForNode(parent);
      var nodePath = NodePath.getForNode(node, parentPath, prop, index);

      return nodePath;
    }

    // Handle actual nodes.
    astTraverse(ast, {
      /**
       * Handler on node enter.
       */
      pre: function pre(node, parent, prop, index) {
        var nodePath = void 0;
        if (!options.asNodes) {
          nodePath = getPathFor(node, parent, prop, index);
        }

        var _iteratorNormalCompletion = true;
        var _didIteratorError = false;
        var _iteratorError = undefined;

        try {
          for (var _iterator = handlers[Symbol.iterator](), _step; !(_iteratorNormalCompletion = (_step = _iterator.next()).done); _iteratorNormalCompletion = true) {
            var handler = _step.value;

            // "Catch-all" `*` handler.
            if (typeof handler['*'] === 'function') {
              if (nodePath) {
                // A path/node can be removed by some previous handler.
                if (!nodePath.isRemoved()) {
                  var handlerResult = handler['*'](nodePath);
                  // Explicitly stop traversal.
                  if (handlerResult === false) {
                    return false;
                  }
                }
              } else {
                handler['*'](node, parent, prop, index);
              }
            }

            // Per-node handler.
            var handlerFuncPre = void 0;
            if (typeof handler[node.type] === 'function') {
              handlerFuncPre = handler[node.type];
            } else if (typeof handler[node.type] === 'object' && typeof handler[node.type].pre === 'function') {
              handlerFuncPre = handler[node.type].pre;
            }

            if (handlerFuncPre) {
              if (nodePath) {
                // A path/node can be removed by some previous handler.
                if (!nodePath.isRemoved()) {
                  var _handlerResult = handlerFuncPre.call(handler, nodePath);
                  // Explicitly stop traversal.
                  if (_handlerResult === false) {
                    return false;
                  }
                }
              } else {
                handlerFuncPre.call(handler, node, parent, prop, index);
              }
            }
          } // Loop over handlers
        } catch (err) {
          _didIteratorError = true;
          _iteratorError = err;
        } finally {
          try {
            if (!_iteratorNormalCompletion && _iterator.return) {
              _iterator.return();
            }
          } finally {
            if (_didIteratorError) {
              throw _iteratorError;
            }
          }
        }
      },
      // pre func

      /**
       * Handler on node exit.
       */
      post: function post(node, parent, prop, index) {
        if (!node) {
          return;
        }

        var nodePath = void 0;
        if (!options.asNodes) {
          nodePath = getPathFor(node, parent, prop, index);
        }

        var _iteratorNormalCompletion2 = true;
        var _didIteratorError2 = false;
        var _iteratorError2 = undefined;

        try {
          for (var _iterator2 = handlers[Symbol.iterator](), _step2; !(_iteratorNormalCompletion2 = (_step2 = _iterator2.next()).done); _iteratorNormalCompletion2 = true) {
            var handler = _step2.value;

            // Per-node handler.
            var handlerFuncPost = void 0;
            if (typeof handler[node.type] === 'object' && typeof handler[node.type].post === 'function') {
              handlerFuncPost = handler[node.type].post;
            }

            if (handlerFuncPost) {
              if (nodePath) {
                // A path/node can be removed by some previous handler.
                if (!nodePath.isRemoved()) {
                  var handlerResult = handlerFuncPost.call(handler, nodePath);
                  // Explicitly stop traversal.
                  if (handlerResult === false) {
                    return false;
                  }
                }
              } else {
                handlerFuncPost.call(handler, node, parent, prop, index);
              }
            }
          } // Loop over handlers
        } catch (err) {
          _didIteratorError2 = true;
          _iteratorError2 = err;
        } finally {
          try {
            if (!_iteratorNormalCompletion2 && _iterator2.return) {
              _iterator2.return();
            }
          } finally {
            if (_didIteratorError2) {
              throw _iteratorError2;
            }
          }
        }
      },
      // post func

      /**
       * Skip locations by default.
       */
      skipProperty: function skipProperty(prop) {
        return prop === 'loc';
      }
    });
  }
};
},{"./node-path":52}],52:[function(require,module,exports){
/**
 * The MIT License (MIT)
 * Copyright (c) 2017-present Dmitry Soshnikov <dmitry.soshnikov@gmail.com>
 */

'use strict';

var _createClass = function () { function defineProperties(target, props) { for (var i = 0; i < props.length; i++) { var descriptor = props[i]; descriptor.enumerable = descriptor.enumerable || false; descriptor.configurable = true; if ("value" in descriptor) descriptor.writable = true; Object.defineProperty(target, descriptor.key, descriptor); } } return function (Constructor, protoProps, staticProps) { if (protoProps) defineProperties(Constructor.prototype, protoProps); if (staticProps) defineProperties(Constructor, staticProps); return Constructor; }; }();

function _classCallCheck(instance, Constructor) { if (!(instance instanceof Constructor)) { throw new TypeError("Cannot call a class as a function"); } }

var DEFAULT_COLLECTION_PROP = 'expressions';
var DEFAULT_SINGLE_PROP = 'expression';

/**
 * NodePath class encapsulates a traversing node,
 * its parent node, property name in the parent node, and
 * an index (in case if a node is part of a collection).
 * It also provides set of methods for AST manipulation.
 */

var NodePath = function () {
  /**
   * NodePath constructor.
   *
   * @param Object node - an AST node
   * @param NodePath parentPath - a nullable parent path
   * @param string property - property name of the node in the parent
   * @param number index - index of the node in a collection.
   */
  function NodePath(node) {
    var parentPath = arguments.length > 1 && arguments[1] !== undefined ? arguments[1] : null;
    var property = arguments.length > 2 && arguments[2] !== undefined ? arguments[2] : null;
    var index = arguments.length > 3 && arguments[3] !== undefined ? arguments[3] : null;

    _classCallCheck(this, NodePath);

    this.node = node;
    this.parentPath = parentPath;
    this.parent = parentPath ? parentPath.node : null;
    this.property = property;
    this.index = index;
  }

  _createClass(NodePath, [{
    key: '_enforceProp',
    value: function _enforceProp(property) {
      if (!this.node.hasOwnProperty(property)) {
        throw new Error('Node of type ' + this.node.type + ' doesn\'t have "' + property + '" collection.');
      }
    }

    /**
     * Sets a node into a children collection or the single child.
     * By default child nodes are supposed to be under `expressions` property.
     * An explicit property can be passed.
     *
     * @param Object node - a node to set into a collection or as single child
     * @param number index - index at which to set
     * @param string property - name of the collection or single property
     */

  }, {
    key: 'setChild',
    value: function setChild(node) {
      var index = arguments.length > 1 && arguments[1] !== undefined ? arguments[1] : null;
      var property = arguments.length > 2 && arguments[2] !== undefined ? arguments[2] : null;


      var childPath = void 0;
      if (index != null) {
        if (!property) {
          property = DEFAULT_COLLECTION_PROP;
        }
        this._enforceProp(property);
        this.node[property][index] = node;
        childPath = NodePath.getForNode(node, this, property, index);
      } else {
        if (!property) {
          property = DEFAULT_SINGLE_PROP;
        }
        this._enforceProp(property);
        this.node[property] = node;
        childPath = NodePath.getForNode(node, this, property, null);
      }
      return childPath;
    }

    /**
     * Appends a node to a children collection.
     * By default child nodes are supposed to be under `expressions` property.
     * An explicit property can be passed.
     *
     * @param Object node - a node to set into a collection or as single child
     * @param string property - name of the collection or single property
     */

  }, {
    key: 'appendChild',
    value: function appendChild(node) {
      var property = arguments.length > 1 && arguments[1] !== undefined ? arguments[1] : null;


      if (!property) {
        property = DEFAULT_COLLECTION_PROP;
      }
      this._enforceProp(property);
      var end = this.node[property].length;
      return this.setChild(node, end, property);
    }

    /**
     * Inserts a node into a collection.
     * By default child nodes are supposed to be under `expressions` property.
     * An explicit property can be passed.
     *
     * @param Object node - a node to insert into a collection
     * @param number index - index at which to insert
     * @param string property - name of the collection property
     */

  }, {
    key: 'insertChildAt',
    value: function insertChildAt(node, index) {
      var property = arguments.length > 2 && arguments[2] !== undefined ? arguments[2] : DEFAULT_COLLECTION_PROP;

      this._enforceProp(property);

      this.node[property].splice(index, 0, node);

      // If we inserted a node before the traversing index,
      // we should increase the later.
      if (index <= NodePath.getTraversingIndex()) {
        NodePath.updateTraversingIndex(+1);
      }

      this._rebuildIndex(this.node, property);
    }

    /**
     * Removes a node.
     */

  }, {
    key: 'remove',
    value: function remove() {
      if (this.isRemoved()) {
        return;
      }
      NodePath.registry.delete(this.node);

      this.node = null;

      if (!this.parent) {
        return;
      }

      // A node is in a collection.
      if (this.index !== null) {
        this.parent[this.property].splice(this.index, 1);

        // If we remove a node before the traversing index,
        // we should increase the later.
        if (this.index <= NodePath.getTraversingIndex()) {
          NodePath.updateTraversingIndex(-1);
        }

        // Rebuild index.
        this._rebuildIndex(this.parent, this.property);

        this.index = null;
        this.property = null;

        return;
      }

      // A simple node.
      delete this.parent[this.property];
      this.property = null;
    }

    /**
     * Rebuilds child nodes index (used on remove/insert).
     */

  }, {
    key: '_rebuildIndex',
    value: function _rebuildIndex(parent, property) {
      var parentPath = NodePath.getForNode(parent);

      for (var i = 0; i < parent[property].length; i++) {
        var path = NodePath.getForNode(parent[property][i], parentPath, property, i);
        path.index = i;
      }
    }

    /**
     * Whether the path was removed.
     */

  }, {
    key: 'isRemoved',
    value: function isRemoved() {
      return this.node === null;
    }

    /**
     * Replaces a node with the passed one.
     */

  }, {
    key: 'replace',
    value: function replace(newNode) {
      NodePath.registry.delete(this.node);

      this.node = newNode;

      if (!this.parent) {
        return null;
      }

      // A node is in a collection.
      if (this.index !== null) {
        this.parent[this.property][this.index] = newNode;
      }

      // A simple node.
      else {
          this.parent[this.property] = newNode;
        }

      // Rebuild the node path for the new node.
      return NodePath.getForNode(newNode, this.parentPath, this.property, this.index);
    }

    /**
     * Updates a node inline.
     */

  }, {
    key: 'update',
    value: function update(nodeProps) {
      Object.assign(this.node, nodeProps);
    }

    /**
     * Returns parent.
     */

  }, {
    key: 'getParent',
    value: function getParent() {
      return this.parentPath;
    }

    /**
     * Returns nth child.
     */

  }, {
    key: 'getChild',
    value: function getChild() {
      var n = arguments.length > 0 && arguments[0] !== undefined ? arguments[0] : 0;

      if (this.node.expressions) {
        return NodePath.getForNode(this.node.expressions[n], this, DEFAULT_COLLECTION_PROP, n);
      } else if (this.node.expression && n == 0) {
        return NodePath.getForNode(this.node.expression, this, DEFAULT_SINGLE_PROP);
      }
      return null;
    }

    /**
     * Whether a path node is syntactically equal to the passed one.
     *
     * NOTE: we don't rely on `source` property from the `loc` data
     * (which would be the fastest comparison), since it might be unsync
     * after several modifications. We use here simple `JSON.stringify`
     * excluding the `loc` data.
     *
     * @param NodePath other - path to compare to.
     * @return boolean
     */

  }, {
    key: 'hasEqualSource',
    value: function hasEqualSource(path) {
      return JSON.stringify(this.node, jsonSkipLoc) === JSON.stringify(path.node, jsonSkipLoc);
    }

    /**
     * JSON-encodes a node skipping location.
     */

  }, {
    key: 'jsonEncode',
    value: function jsonEncode() {
      var _ref = arguments.length > 0 && arguments[0] !== undefined ? arguments[0] : {},
          format = _ref.format,
          useLoc = _ref.useLoc;

      return JSON.stringify(this.node, useLoc ? null : jsonSkipLoc, format);
    }

    /**
     * Returns previous sibling.
     */

  }, {
    key: 'getPreviousSibling',
    value: function getPreviousSibling() {
      if (!this.parent || this.index == null) {
        return null;
      }
      return NodePath.getForNode(this.parent[this.property][this.index - 1], NodePath.getForNode(this.parent), this.property, this.index - 1);
    }

    /**
     * Returns next sibling.
     */

  }, {
    key: 'getNextSibling',
    value: function getNextSibling() {
      if (!this.parent || this.index == null) {
        return null;
      }
      return NodePath.getForNode(this.parent[this.property][this.index + 1], NodePath.getForNode(this.parent), this.property, this.index + 1);
    }

    /**
     * Returns a NodePath instance for a node.
     *
     * The same NodePath can be reused in several places, e.g.
     * a parent node passed for all its children.
     */

  }], [{
    key: 'getForNode',
    value: function getForNode(node) {
      var parentPath = arguments.length > 1 && arguments[1] !== undefined ? arguments[1] : null;
      var prop = arguments.length > 2 && arguments[2] !== undefined ? arguments[2] : null;
      var index = arguments.length > 3 && arguments[3] !== undefined ? arguments[3] : -1;

      if (!node) {
        return null;
      }

      if (!NodePath.registry.has(node)) {
        NodePath.registry.set(node, new NodePath(node, parentPath, prop, index == -1 ? null : index));
      }

      var path = NodePath.registry.get(node);

      if (parentPath !== null) {
        path.parentPath = parentPath;
        path.parent = path.parentPath.node;
      }

      if (prop !== null) {
        path.property = prop;
      }

      if (index >= 0) {
        path.index = index;
      }

      return path;
    }

    /**
     * Initializes the NodePath registry. The registry is a map from
     * a node to its NodePath instance.
     */

  }, {
    key: 'initRegistry',
    value: function initRegistry() {
      if (!NodePath.registry) {
        NodePath.registry = new Map();
      }
      NodePath.registry.clear();
    }

    /**
     * Updates index of a currently traversing collection.
     */

  }, {
    key: 'updateTraversingIndex',
    value: function updateTraversingIndex(dx) {
      return NodePath.traversingIndexStack[NodePath.traversingIndexStack.length - 1] += dx;
    }

    /**
     * Returns current traversing index.
     */

  }, {
    key: 'getTraversingIndex',
    value: function getTraversingIndex() {
      return NodePath.traversingIndexStack[NodePath.traversingIndexStack.length - 1];
    }
  }]);

  return NodePath;
}();

NodePath.initRegistry();

/**
 * Index of a currently traversing collection is stored on top of the
 * `NodePath.traversingIndexStack`. Remove/insert methods can adjust
 * this index.
 */
NodePath.traversingIndexStack = [];

// Helper function used to skip `loc` in JSON operations.
function jsonSkipLoc(prop, value) {
  if (prop === 'loc') {
    return undefined;
  }
  return value;
}

module.exports = NodePath;
},{}],53:[function(require,module,exports){
/**
 * The MIT License (MIT)
 * Copyright (c) 2017-present Dmitry Soshnikov <dmitry.soshnikov@gmail.com>
 */

'use strict';

/**
 * Performs a deep copy of an simple object.
 * Only handles scalar values, arrays and objects.
 *
 * @param obj Object
 */

module.exports = function clone(obj) {
  if (obj === null || typeof obj !== 'object') {
    return obj;
  }
  var res = void 0;
  if (Array.isArray(obj)) {
    res = [];
  } else {
    res = {};
  }
  for (var i in obj) {
    res[i] = clone(obj[i]);
  }
  return res;
};
},{}],54:[function(require,module,exports){
/**
 * The MIT License (MIT)
 * Copyright (c) 2017-present Dmitry Soshnikov <dmitry.soshnikov@gmail.com>
 */

'use strict';

module.exports = require('./dist/regexp-tree');
},{"./dist/regexp-tree":48}],55:[function(require,module,exports){
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.PerformanceObserver = exports.performance = void 0;
exports.performance = window.performance, exports.PerformanceObserver = window.PerformanceObserver;

},{}],56:[function(require,module,exports){
/* eslint-disable no-use-before-define */
/* eslint-disable no-case-declarations */
/* eslint-disable default-case */
const { concat } = require('lodash');

const { DFA_NODE_TYPE } = require('../constants');

module.exports.convertToBasicOperators = (str = '') => {
  const positiveGrouped = /\(([^()]+)\)\+/;
  const positive = /[a-z|A-Z|0-9]\+/;
  const positiveGroupedMatch = str.match(positiveGrouped);
  const positiveMatch = str.match(positive);

  const positiveGroupedStr = positiveGroupedMatch !== null ? positiveGroupedMatch[0].replace('+', '') : null;
  const positiveStr = positiveMatch !== null ? positiveMatch[0].replace('+', '') : null;

  const unaryGrouped = /\(([^()]+)\)\?/;
  const unary = /[a-z|A-Z|0-9]\?/;
  const unaryGroupedMatch = str.match(unaryGrouped);
  const unaryMatch = str.match(unary);

  const unaryGroupedStr = unaryGroupedMatch !== null ? unaryGroupedMatch[0].replace('?', '') : null;
  const unaryStr = unaryMatch !== null ? unaryMatch[0].replace('?', '') : null;

  str = str.replace(`${positiveGroupedStr}+`, `${positiveGroupedStr + positiveGroupedStr}*`)
    .replace(`${positiveStr}+`, `${positiveStr + positiveStr}*`)
    .replace(`${unaryGroupedStr}?`, `(${unaryGroupedStr}|ε)`)
    .replace(`${unaryStr}?`, `(${unaryStr}|ε)`);
  return str;
};

module.exports.calculatedFunctions = (syntacticTree) => {
  const calculateOr = (or) => {
    if (or.left.type === DFA_NODE_TYPE.leaf) {
      or.left.nullable = or.left.id === 0;
      or.left.firstPosition = [or.left.id];
      or.left.lastPosition = [or.left.id];
    } else {
      or.left = calculateNode(or.left);
    }

    if (or.right.type === DFA_NODE_TYPE.leaf) {
      or.right.nullable = or.right.id === 0;
      or.right.firstPosition = [or.right.id];
      or.right.lastPosition = [or.right.id];
    } else {
      or.right = calculateNode(or.right);
    }
    or.nullable = or.left.nullable || or.right.nullable;
    or.firstPosition = concat(or.left.firstPosition, or.right.firstPosition);
    or.lastPosition = concat(or.left.lastPosition, or.right.lastPosition);
    return or;
  };

  const calculateGroup = (group) => {
    group.children.forEach((child) => {
      if (child.type === DFA_NODE_TYPE.leaf) {
        child.nullable = child.id === 0;
        child.firstPosition = child.id === 0 ? [] : [child.id];
        child.lastPosition = child.id === 0 ? [] : [child.id];
      } else {
        child = calculateNode(child);
      }
    });

    group.nullable = group.children[group.children.length - 1].nullable;
    group.firstPosition = group.children[group.children.length - 1].firstPosition;
    group.lastPosition = group.children[group.children.length - 1].lastPosition;
    return group;
  };

  const calculateNode = (node) => {
    switch (node.label) {
      case 'GROUP':
        node = calculateGroup(node);
        break;
      case 'CONCAT':
        node = calculateGroup(node);
        let nullable = !!node.children[0].nullable;
        let firstPosition = [];
        let lastPosition = [];
        node.children.forEach((concatChild, index) => {
          nullable = nullable && concatChild.nullable;

          if (index === 0) {
            firstPosition = concatChild.firstPosition;
          } else {
            const beforeChild = node.children[index - 1];
            if (beforeChild.nullable) {
              firstPosition = concat(firstPosition, concatChild.firstPosition);
            }
          }

          if (concatChild.nullable) {
            lastPosition = concat(lastPosition, concatChild.lastPosition);
          } else {
            lastPosition = concatChild.lastPosition;
          }
        });

        node.nullable = nullable;
        node.firstPosition = firstPosition;
        node.lastPosition = lastPosition;
        break;
      case 'KLEEN':
        node = calculateGroup(node);
        node.nullable = true;
        break;
      case 'OR':
        node = calculateOr(node);
        break;
    }

    return node;
  };

  syntacticTree.children.forEach((child) => {
    if (child.type === DFA_NODE_TYPE.leaf) {
      child.nullable = child.id === 0;
      child.firstPosition = child.id === 0 ? [] : [child.id];
      child.lastPosition = child.id === 0 ? [] : [child.id];
    } else {
      child = calculateGroup(child);
    }
  });

  if (syntacticTree.children[0].nullable) {
    syntacticTree.firstPosition = concat(
      syntacticTree.children[0].firstPosition,
      syntacticTree.children[1].firstPosition,
    );
  } else {
    syntacticTree.firstPosition = syntacticTree.children[0].firstPosition;
  }

  if (syntacticTree.children[1].nullable) {
    syntacticTree.lastPosition = concat(
      syntacticTree.children[0].lastPosition,
      syntacticTree.children[1].lastPosition,
    );
  } else {
    syntacticTree.lastPosition = syntacticTree.children[1].lastPosition;
  }

  return syntacticTree;
};

},{"../constants":9,"lodash":10}],"regparser":[function(require,module,exports){
const DirectDFA = require('./DirectDFA');
const FSM = require('./FSM');
const NFA = require('./NFA');
const RegParser = require('./RegParser');

module.exports = {
  DirectDFA,
  FSM,
  NFA,
  RegParser,
};

},{"./DirectDFA":2,"./FSM":4,"./NFA":6,"./RegParser":8}]},{},[]);
