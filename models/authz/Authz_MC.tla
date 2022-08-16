------------------------------- MODULE Authz_MC --------------------------------
(******************************************************************************)

(******************************************************************************)
EXTENDS Authz

const_Address == {"a1", "a2"}
const_Validators ==  {"v1"}

const_msgTypeUrls == {"foo"}
const_Authorization == {NoAuthorization}
const_Accept(auth,msg) == [accept |-> TRUE, delete |-> FALSE, updated |-> NoAuthorization, error |-> "none"]
const_MsgTypeURL(auth) == "foo"
const_SdkMsgContent == {"x", "y"} 

--------------------------------------------------------------------------------

View == <<grantStore>>

================================================================================
