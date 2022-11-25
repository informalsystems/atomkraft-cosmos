------------------------------ MODULE MsgTypes --------------------------------
(******************************************************************************)
(* SDK message type URLs                                                      *)
(******************************************************************************)

\* @typeAlias: msgTypeUrl = Str;
\* @type: $msgTypeUrl;
SEND_TYPE_URL == "send"

\* @type: $msgTypeUrl;
DELEGATE_TYPE_URL == "delegate"

\* @type: $msgTypeUrl;
UNDELEGATE_TYPE_URL == "undelegate"

\* @type: $msgTypeUrl;
BEGIN_REDELEGATE_TYPE_URL == "redelegate"

MsgTypes == {
    SEND_TYPE_URL, 
    DELEGATE_TYPE_URL, 
    UNDELEGATE_TYPE_URL, 
    BEGIN_REDELEGATE_TYPE_URL
}

\* @typeAlias: account = Str;
\* @typeAlias: coins = Int;
\* @typeAlias: validator = Str;
\* @typeAlias: auth = {type: Str, msgTypeUrl: $msgTypeUrl, validators: Set($validator), allow: Bool, spendLimit: $coins, allowList: Set($account)};
TypeAliases == TRUE

================================================================================
Created by Hernán Vanzetto on 6 September 2022
