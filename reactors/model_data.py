from datetime import datetime, timedelta
from enum import Enum
from typing import Dict, List, Optional, Union

from terra_sdk.core import authz as terra
from terra_sdk.util.converter import to_isoformat

# STAKE_AUTH_TYPE = {
#     "msg_delegate": AuthorizationType.AUTHORIZATION_TYPE_DELEGATE,
#     "msg_undelegate": AuthorizationType.AUTHORIZATION_TYPE_UNDELEGATE,
#     "msg_redelegate": AuthorizationType.AUTHORIZATION_TYPE_REDELEGATE,
#     "msg_alpha": AuthorizationType.AUTHORIZATION_TYPE_UNSPECIFIED,
# }

accounts = ["a1", "a2", "a3"]
validators = ["v1", "v2", "v3"]

Address = str
Coins = int

NO_MAX_COINS = -99


class MsgTypeUrls(Enum):
    generic = 1
    send = 2
    delegate = 3
    undelegate = 4
    redelegate = 5


class ExpirationTime(Enum):
    past = 1
    future = 2
    none = 3
    expire_soon = 4


def to_real_time(expiration_time: ExpirationTime):
    match expiration_time:
        case "past":
            return to_isoformat(datetime.now() - timedelta(seconds=100))
        case "future":
            return to_isoformat(datetime.now() + timedelta(seconds=100))
        case "expire_soon":
            return to_isoformat(datetime.now() + timedelta(seconds=10))
        case "none":
            # terra.py client requires a concrete timestamp
            return to_isoformat(datetime.now() + timedelta(seconds=10000))


class GenericAuthorization:
    authorizationType: MsgTypeUrls

    def mk_grant(self, testnet) -> terra.AuthorizationGrant:
        return terra.GenericAuthorization(msg="msg_alpha")


class GenericSdkMsgContent:
    typeUrl: MsgTypeUrls  # .generic


class SendAuthorization:
    authorizationType: MsgTypeUrls
    spendLimit: Coins
    allowList: List[Address]


class SendSdkMsgContent:
    typeUrl: MsgTypeUrls  # .send
    fromAddress: Address
    toAddress: Address
    amount: Coins


class StakeAuthorization:
    maxTokens: Optional[Coins]
    validators: List[Address]
    allow: bool
    authorizationType: MsgTypeUrls


class MsgDelegate:
    typeUrl: MsgTypeUrls  # .delegate
    delegatorAddress: Address
    validatorAddress: Address
    amount: Coins


class MsgUndelegate:
    typeUrl: MsgTypeUrls  # .undelegate
    delegatorAddress: Address
    validatorAddress: Address
    amount: Coins


class MsgBeginRedelegate:
    typeUrl: MsgTypeUrls  # .redelegate
    delegatorAddress: Address
    validatorSrcAddress: Address
    validatorDstAddress: Address
    amount: Coins


StakeSdkMsgContent = Union[MsgDelegate, MsgUndelegate, MsgBeginRedelegate]

Authorization = Union[GenericAuthorization, SendAuthorization, StakeAuthorization]


class Grant:
    authorization: Authorization
    expirationTime: ExpirationTime


SdkMsgContent = Union[GenericSdkMsgContent, SendSdkMsgContent, StakeSdkMsgContent]


class GrantIds:
    granter: Address
    grantee: Address
    msgTypeUrl: MsgTypeUrls


class MsgGrant:
    type: str = "grant"
    granter: Address
    grantee: Address
    grant: Grant


class MsgRevoke:
    type: str = "revoke"
    granter: Address
    grantee: Address
    msgTypeUrl: MsgTypeUrls


class SdkMsgs:
    signer: Address
    content: SdkMsgContent


class MsgExec:
    type: str = "exec"
    grantee: Address
    msg: SdkMsgs


RequestMessages = Union[MsgGrant, MsgRevoke, MsgExec]


class ExpireEvent:
    type: str = "expire"
    grantId: GrantIds


Event = Union[RequestMessages, ExpireEvent]

GrantStore = Dict[GrantIds, Grant]


def get_grant(grantStore: GrantStore, grantId: GrantIds):
    for k, v in grantStore.items():
        if k == grantId:
            return v

    return None


## Responses

MsgResponseErrors = str


class Response:
    type: str
    ok: bool
    error: Optional[MsgResponseErrors]
