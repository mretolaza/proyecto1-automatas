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
