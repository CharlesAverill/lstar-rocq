# v3.0

Breaking changes.
Teacher modules have changed substantially.
TTT for DFAs, L* for Moore and Mealy machines are now supported.

# v2.0

Breaking changes.
Both L* and KV signatures have changed, requiring passing fuel in via the `Teacher`
module rather than upon calling the learner loop.
This arises from new guarantees about termination and minimality for both algorithms.

# v1.0

Initial release
