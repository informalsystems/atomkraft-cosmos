------------------------------- MODULE Authz_MC --------------------------------
(******************************************************************************)

(******************************************************************************)
EXTENDS Authz

instance_Address == {"a1", "a2"}

instance_Coins == {0,1}

instance_GenericMsgTypeUrl == "generic/msg/type"

--------------------------------------------------------------------------------

\* View == <<grantStore>>

================================================================================
