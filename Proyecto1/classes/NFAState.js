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
