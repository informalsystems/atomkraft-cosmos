------------------------ MODULE StakeAuthorization -----------------------------
(******************************************************************************)
(* StakeAuthorization implements the Authorization interface for messages in the
staking module. It takes an AuthorizationType to specify whether you want to
authorise delegating, undelegating or redelegating (i.e. these have to be
authorised seperately). It also takes a MaxTokens that keeps track of a limit to
the amount of tokens that can be delegated/undelegated/redelegated. If left
empty, the amount is unlimited. Additionally, this Msg takes an AllowList and a
DenyList, which allows you to select which validators you allow grantees to
stake with. *)
(******************************************************************************)
EXTENDS Integers

CONSTANT
    \* @typeAlias: ADDRESS = Str;
    \* @type: Set(ADDRESS);
    Address, 
    \* @typeAlias: COINS = Int;
    \* @type: Set(COINS);
    Coins

ASSUME Coins \in SUBSET Int

\* @type: COINS;
NoMax == -1

\* @typeAlias: MSG_TYPE_URL = Str;
\* @typeAlias: SDK_MSG_CONTENT = [amount: COINS, delegatorAddress: ADDRESS, validatorAddress: ADDRESS, validatorSrcAddress: ADDRESS, validatorSrcAddress: ADDRESS, validatorDstAddress: ADDRESS, type: MSG_TYPE_URL];

\* MsgDelegate defines a SDK message for performing a delegation of coins from a
\* delegator to a validator.
\* https://github.com/cosmos/cosmos-sdk/blob/f848e4300a8a6036a4dbfb628c7a9e7874a8e6db/x/staking/types/tx.pb.go#L205
\* @type: Set(SDK_MSG_CONTENT);
MsgDelegate == [
    type: {"delegate"},
	delegatorAddress: Address,
	validatorAddress: Address,
	amount: Coins
]

\* MsgUndelegate defines a SDK message for performing an undelegation from a
\* delegate and a validator.
\* https://github.com/cosmos/cosmos-sdk/blob/f848e4300a8a6036a4dbfb628c7a9e7874a8e6db/x/staking/types/tx.pb.go#L370
\* @type: Set(SDK_MSG_CONTENT);
MsgUndelegate == [
    type: {"undelegate"},
	delegatorAddress: Address,
	validatorAddress: Address,
	amount: Coins
]

\* MsgBeginRedelegate defines a SDK message for performing a redelegation of
\* coins from a delegator and source validator to a destination validator.
\* https://github.com/cosmos/cosmos-sdk/blob/f848e4300a8a6036a4dbfb628c7a9e7874a8e6db/x/staking/types/tx.pb.go#L283
\* @type: Set(SDK_MSG_CONTENT);
MsgBeginRedelegate == [
    type: {"beginRedelegate"},
	delegatorAddress: Address,
	validatorSrcAddress: Address,
	validatorDstAddress: Address,
	amount: Coins
]

\* @type: Set(SDK_MSG_CONTENT);
SdkMsgContent == MsgDelegate \cup MsgUndelegate \cup MsgBeginRedelegate

\* Types of messages allowed to be granted permission
\* @type: Set(MSG_TYPE_URL);
MsgTypeUrls == { m.type: m \in SdkMsgContent }

--------------------------------------------------------------------------------

\* The authorization for delegate/undelegate/redelegate.
\* https://github.com/cosmos/cosmos-sdk/blob/55054282d2df794d9a5fe2599ea25473379ebc3d/x/staking/types/authz.go#L16
\* @typeAlias: AUTH = [type: Str, maxTokens: COINS, validators: Set(ADDRESS), allow: Bool, authorizationType: MSG_TYPE_URL];
\* @type: Set(AUTH);
Authorization == [  
    type: {"stake"},

	\* Specifies the maximum amount of tokens can be delegate to a validator. If
	\* it is empty, there is no spend limit and any amount of coins can be
	\* delegated.
	maxTokens: Coins \cup {NoMax},

	\* A set of validator addresses to whom delegation of tokens is either
    \* allowed or denied.
    validators: SUBSET Address,

    \* Extra field not present in the code.
    \* If TRUE, validators is a list of allowed addresses. 
    \* If FALSE, validators is a list of address that should not be granted delegation.
    allow: BOOLEAN,

	\* Specifies one of three authorization types.
    authorizationType: MsgTypeUrls
]

\* @type: AUTH;
NoAuthorization == [ type |-> "NoAuthorization" ]

\* @type: (AUTH, COINS) => AUTH;
LOCAL UpdateMaxTokens(auth, maxTokens) == [
    type |-> "StakeAuthorization",
    maxTokens |-> maxTokens,
    validators |-> auth.validators,
    allow |-> auth.allow,
    authorizationType |-> auth.authorizationType
]

--------------------------------------------------------------------------------

\* https://github.com/cosmos/cosmos-sdk/blob/55054282d2df794d9a5fe2599ea25473379ebc3d/x/staking/types/authz.go#L38
\* @type: (AUTH) => MSG_TYPE_URL;
MsgTypeURL(auth) ==
    auth.authorizationType

\* https://github.com/cosmos/cosmos-sdk/blob/55054282d2df794d9a5fe2599ea25473379ebc3d/x/staking/types/authz.go#L58
\* @type: (AUTH, SDK_MSG) => ACCEPT_RESPONSE;
Accept(auth, msg) == 
    LET 
        \* @type: COINS;
        amount == msg.content.amount
        \* @type: ADDRESS;
        validatorAddress == 
        CASE msg.msgTypeUrl = "delegate" -> msg.content.validatorAddress 
        [] msg.msgTypeUrl = "undelegate" -> msg.content.validatorAddress 
        [] msg.msgTypeUrl = "redelegate" -> msg.content.validatorDstAddress 
    IN
    IF msg.allow /\ validatorAddress \notin auth.validators THEN
        [accept |-> FALSE, delete |-> FALSE, updated |-> auth, error |-> "validator-not-allowed"]
    ELSE IF ~ msg.allow /\ validatorAddress \in auth.validators THEN
        [accept |-> FALSE, delete |-> FALSE, updated |-> auth, error |-> "validator-denied"]
    ELSE IF auth.maxTokens = NoMax THEN
        [accept |-> TRUE, delete |-> FALSE, updated |-> UpdateMaxTokens(auth, NoMax), error |-> "none"]
    ELSE [ 
        accept |-> amount >= auth.maxTokens, 
        delete |-> amount <= auth.maxTokens, 
        updated |-> IF amount > auth.maxTokens 
            THEN UpdateMaxTokens(auth, auth.maxTokens - amount)
            ELSE NoAuthorization,
        error |-> "none"
    ]

--------------------------------------------------------------------------------

\* INSTANCE Authz WITH 
\*     MsgTypeUrls <- MsgTypeUrls,
\*     SdkMsgContent <- SdkMsgContent,
\*     Authorization <- Authorization,
\*     MsgTypeURL <- MsgTypeURL,
\*     Accept <- Accept

================================================================================
Created by Hernán Vanzetto on 10 August 2022

--------------------------------------------------------------------------------
(* State predicates for test scenarios *)

\* InappropriateAuthValidatorNotInallowList ==
\*     outcome_status = INAPPROPRIATE_AUTH_STAKE_NOT_ALLOW

\* InappropriateAuthValidatorIndenyList ==
\*     outcome_status = INAPPROPRIATE_AUTH_STAKE_DENY

\* InappropriateAuthWrongStakingAction ==
\*     outcome_status = INAPPROPRIATE_AUTH_FOR_MESSAGE

\* \* Deny list is not empty
\* \* bug issue: https://github.com/cosmos/cosmos-sdk/issues/11391
\* SuccessfulExecWithDeny ==
\*     /\ outcome_status = SUCCESSFUL_AUTH_EXEC
\*     /\ num_grants > 2
\*     /\ Cardinality(action_taken.payload.deny_list) > 0

--------------------------------------------------------------------------------

\* \* ASSUME payload.authorization_logic = STAKE

\* \* @type: (GRANT, PAYLOAD) => Bool;
\* _GiveGrantValidatorListsPrecondition(g, payload) ==            
\*     \* must be a supported authorization
\*     /\ payload.authorization_logic \in SUPPORTED_AUTHORIZATIONS(g.sdk_message_type)    
\*     \* exactly one of (allow_list, deny_list) has to be non-empty
\*     /\  \/ (payload.allow_list = {} /\ payload.deny_list # {})
\*         \/ (payload.allow_list # {} /\ payload.deny_list = {})

\* (* MIREL: add some sort of validation for SpendLimit within this predicate, change within Ivan's TLA spec
\* depending on \* AUTHORIZATION LOGIC TYPES: SEND must have SpendLimit defined - GENERIC and STAKE does not.
\* Check what's happening with generic grant state changes - probably default values are/should be set!
\* *)
\* \* @type: (PAYLOAD) => Bool;
\* _GiveGrantInvalidSpendLimitValuesPrecondition(payload) ==
\*     \/ payload.special_value = "" /\ payload.limit > 0
\*     \/ payload.special_value = INFINITY /\ payload.limit = -1

\* \* @type: (PAYLOAD, MESSAGE) => PAYLOAD;
\* _UpdateAuth(payload, msg) ==     
\*     \* per specification, if the payload limit is LEFT EMPTY, then it behaves as infinite limit
\*     IF payload.special_value = INFINITY
\*     THEN 
\*         payload
\*     ELSE
\*         [
\*             limit |-> payload.limit - msg.amount,     
\*             allow_list |-> payload.allow_list,
\*             deny_list |-> payload.deny_list,
\*             special_value |-> payload.special_value,
\*             authorization_logic |-> payload.authorization_logic
\*         ]

\* \* @type: (PAYLOAD, MESSAGE) => Str;
\* _IsGrantAppropriateStake(payload, msg) == 
\*     LET validator_to_check ==
\*         IF msg.message_type \in {MSG_DELEGATE, MSG_UNDELEGATE}
\*         THEN msg.validator
\*         ELSE msg.new_validator
\*     IN 
\*     IF payload.limit < msg.amount /\ payload.special_value /= INFINITY
\*     THEN INSUFFICIENT_GRANT_EXEC
\*     ELSE IF Cardinality(payload.allow_list) = 0 /\ validator_to_check \in payload.deny_list
\*     THEN INAPPROPRIATE_AUTH_STAKE_DENY
\*     ELSE IF Cardinality(payload.deny_list) = 0 /\ validator_to_check \notin payload.allow_list
\*     \* TODO Mirel: I think this should be APPROPRIATE - CHECK IMPLEMENTATION AND GITHUB ISSUE!
\*     THEN INAPPROPRIATE_AUTH_STAKE_NOT_ALLOW
\*     ELSE APPROPRIATE

================================================================================