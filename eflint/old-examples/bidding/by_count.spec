Fact bidder
  Present When True

Fact object
  Present When True

Fact auctioneer Identified by Auctioneer

Fact bid counter 
  Identified by Int
  Derived from Count (Foreach bidder, object:
Fact bid Identified by bidder * object

Fact place bid
  Actor bidder
  Recipient auctioneer
  Related to object
  Creates bid()


