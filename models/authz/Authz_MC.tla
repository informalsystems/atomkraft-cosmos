------------------------------- MODULE Authz_MC --------------------------------
(******************************************************************************)

(******************************************************************************)
EXTENDS Authz

const_Address == {"a1", "a2"}

const_msgTypeUrls == {"delegate"}
const_Authorization == {NoAuthorization}
const_Accept(auth,msg) == [accept |-> TRUE, delete |-> FALSE, updated |-> NoAuthorization, error |-> "none"]
const_MsgTypeURL(auth) == "delegate"
const_SdkMsgContent == {"x", "y"} 

const_Coins == {0,1}

const_GenericMsgTypeUrl == "generic/msg/type"

--------------------------------------------------------------------------------

View == <<grantStore>>

================================================================================
