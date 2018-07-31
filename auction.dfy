include "ctrct.dfy"

class Auction extends Contract {
  var beneficiary: Contract;
  var auctionEnd: nat;

  var highestBidder: Contract?;
  var highestBid: nat;

  var pendingReturns: map<Contract, nat>;

  var ended: bool;

  constructor(biddingTime: nat, seller: Contract, block: Block)
    ensures beneficiary == seller && auctionEnd == block.timestamp + biddingTime;
  {
    beneficiary := seller;
	  auctionEnd := block.timestamp + biddingTime;
	  highestBidder := null;
    highestBid := 0;
    ended := false;
    pendingReturns := map[];
  }

  predicate bidChange(oldBidder: Contract, oldBid: nat, oldPending: map<Contract, nat>)
    reads this
    requires oldBidder in pendingReturns
  {
    var oldValue := if oldBidder in oldPending then oldPending[oldBidder] else 0;
    pendingReturns[oldBidder] == oldValue + oldBid
  }

  predicate balanceSafety()
    reads this
  {
    Balance >= highestBid
      && forall a | a in pendingReturns :: Balance >= pendingReturns[a]
  }

  method bid(block: Block, msg: Message)
    modifies this
    requires block.timestamp <= auctionEnd
    requires msg.value > highestBid
    requires highestBid == 0 <==> highestBidder == null
    requires balanceSafety()
    ensures balanceSafety()
    ensures highestBidder == msg.sender && highestBid == msg.value
    ensures old(highestBidder) != null ==> old(highestBidder) in pendingReturns && bidChange(old(highestBidder), old(highestBid), old(pendingReturns))
  {
      Balance := Balance + msg.value;
      if (highestBid != 0) {
          var oldValue := if highestBidder in pendingReturns then pendingReturns[highestBidder] else 0;
          pendingReturns := pendingReturns[highestBidder := oldValue + highestBid];
      }
      highestBidder := msg.sender;
      highestBid := msg.value;
      // emit HighestBidIncreased(msg.sender, msg.value);
  }

  method withdraw(block: Block, msg: Message) returns (ret: bool)
    modifies this, msg.sender
    requires msg.sender in pendingReturns
    requires msg.sender != this
    requires balanceSafety()
    ensures msg.sender in pendingReturns
    ensures ret ==> Balance == old(Balance) - old(pendingReturns[msg.sender])
    // ensures balanceSafety()
  {
    var amount := pendingReturns[msg.sender];
    if (amount > 0) {
      pendingReturns := pendingReturns[msg.sender := 0];

      var sendSuccess := send(this, msg.sender, amount);
      if (!sendSuccess) {
        pendingReturns := pendingReturns[msg.sender := amount];
        ret := false;
      }
      else {
        pendingReturns := pendingReturns[msg.sender := 0];
        ret := true;
      }
      assert sendSuccess <==> ret;
    }
    else {
      ret := true;
    }
  }

  method endAuction(block: Block, msg: Message) returns (exception: bool)
    modifies this, beneficiary
    requires block.timestamp >= auctionEnd
    requires !ended
    requires beneficiary != this
    requires balanceSafety()
    ensures !exception ==> Balance == old(Balance) - old(highestBid)
    // ensures balanceSafety()
  {
    ended := true;
    // emit AuctionEnded(highestBidder, highestBid);

    exception := transfer(this, beneficiary, highestBid);
  }
}
