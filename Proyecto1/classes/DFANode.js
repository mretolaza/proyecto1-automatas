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
