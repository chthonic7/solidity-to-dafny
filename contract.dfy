trait Contract {
  ghost var GlobalSpace: map<nat, Contract>;
  var Balance: int;

  method fallback(from: Contract, amount: int) returns (exception: bool)
    modifies this
    ensures !exception ==> Balance == old(Balance) + amount
  {
    Balance := Balance + amount;
    exception := FallbackSpec();
  }

  method FallbackSpec() returns (exception: bool)
    ensures this == old(this)
  {
  }
}

method transfer(from: Contract, to: Contract, amount: nat) returns (exception: bool)
  modifies from, to
  requires from != to && from.Balance >= amount
  ensures !exception ==> from.Balance == old(from.Balance) - amount && to.Balance == old(to.Balance) + amount
{
  from.Balance := from.Balance - amount;
  exception := to.fallback(from, amount);
}

method send(from: Contract, to: Contract, amount: int) returns (success: bool)
  modifies from, to
  requires from != to && from.Balance >= amount
  ensures success ==> from.Balance == old(from.Balance) - amount && to.Balance == old(to.Balance) + amount
{
  from.Balance := from.Balance - amount;
  var failed := to.fallback(from, amount);
  success := !failed;
}

class Block {
  var timestamp: nat;
}

class Message {
  var sender: Contract;
  var value: int;

  constructor (s: Contract, v: int)
    ensures sender == s && value == v
  {
    sender := s;
    value := v;
  }
}
