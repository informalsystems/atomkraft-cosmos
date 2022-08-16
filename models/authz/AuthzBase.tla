------------------------------ MODULE AuthzBase --------------------------------
(******************************************************************************)

(******************************************************************************)

\* @typeAlias: ADDRESS = Str;
\* @typeAlias: VALIDATORS = Str;

CONSTANTS
    \* @type: Set(ADDRESS);
    Address,
    
    \* @type: Set(VALIDATORS);
    Validators

\* @typeAlias: AUTH_TYPE = Str;
\* @typeAlias: COINS = Int;
\* @typeAlias: EXPIRATION_TIME = Str;
\* @typeAlias: MSG_TYPE_URL = Str;

\* @ typeAlias: AUTH = [ 
\*     type: Str, 
\*     spendLimit: COINS,
\*     allowList: Set(ADDRESS),
\*     maxTokens: COINS, 
\*     validators: VALIDATORS,
\*     allow: Bool,
\*     authorizationType: AUTH_TYPE,
\*     ];

--------------------------------------------------------------------------------

\* @typeAlias: AUTH = [type: Str, spendLimit: COINS, allowList: Set(ADDRESS), maxTokens: COINS, validators: VALIDATORS, allow: Bool, authorizationType: AUTH_TYPE];
\* @type: AUTH;
NoAuthorization == [ type |-> "NoAuthorization" ]

================================================================================
Created by Hernán Vanzetto on 10 August 2022
