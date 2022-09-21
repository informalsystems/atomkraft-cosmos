from enum import Enum
from typing import Dict, List, Optional, Union


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


EXPIRES_SOON_TIME = 5


class GenericAuthorization:
    msgTypeUrl: MsgTypeUrls

    # def to_real(self):
    #     return GenericAuthorization(msg=MSG_TYPE[self.msgTypeUrl])


class GenericSdkMsgContent:
    typeUrl: MsgTypeUrls  # .generic


class SendAuthorization:
    msgTypeUrl: MsgTypeUrls
    spendLimit: Coins
    allowList: List[Address]

    # def to_real(self, testnet: Testnet):
    #     return SendAuthorization(spend_limit=to_real_coins(testnet, self.spendLimit))


class SendSdkMsgContent:
    typeUrl: MsgTypeUrls  # .send
    fromAddress: Address
    toAddress: Address
    amount: Coins

    # def to_real(self, testnet: Testnet):
    #     return TerraBank.MsgSend(
    #         from_address=testnet.val_addr(self.fromAddress, True),
    #         to_address=testnet.val_addr(self.toAddress, True),
    #         amount=to_real_coins(testnet, self.amount),
    #     )


Validators = List[Address]


# def validators_to_real(validators: Validators, testnet: Testnet):
#     addresses = [testnet.val_addr(address, True) for address in validators]
#     return StakeAuthorizationValidators(addresses)


class StakeAuthorization:
    maxTokens: Optional[Coins]
    validators: List[Address]
    allow: bool
    msgTypeUrl: MsgTypeUrls

    # def to_real(self, testnet: Testnet):
    #     validators = validators_to_real(self.validators, testnet)
    #     return StakeAuthorization(
    #         authorization_type=STAKING_AUTH_TYPE[self.msgTypeUrl],
    #         max_tokens=to_real_coins(testnet, self.maxTokens),
    #         allow_list=validators if self.allow else None,
    #         deny_list=validators if not self.allow else None,
    #     )


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


# def authorization_to_real(auth: Authorization, testnet: Testnet):
#     return auth.to_real(testnet)
# match auth.msgTypeUrl:
#     case MsgTypeUrls.send:
#         # auth: SendAuthorization = auth
#         return auth.to_real(testnet)
#     case MsgTypeUrls.delegate | MsgTypeUrls.undelegate | MsgTypeUrls.redelegate:
#         return to_real_stake_auth(testnet, auth)
#     case _:
#         return to_real_generic_auth(auth)


class Grant:
    authorization: Authorization
    expirationTime: ExpirationTime

    # def to_real(self, testnet: Testnet):
    #     return terra.AuthorizationGrant(
    #         authorization=authorization_to_real(self.authorization, testnet),
    #         expiration=to_real_time(self.expirationTime),
    #     )


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


#     def to_real_msg_send(self, testnet: Testnet):
#         return TerraBank.MsgSend(
#             from_address=testnet.val_addr(self.content.fromAddress, True),
#             to_address=testnet.val_addr(self.content.toAddress, True),
#             amount=to_real_coins(testnet, self.content.amount),
#         )

#     def to_real_msg_delegate(self, testnet: Testnet):
#         return TerraStaking.MsgDelegate(
#             delegator_address=testnet.acc_addr(self.signer),
#             validator_address=testnet.val_addr(self.content.validatorAddress, True),
#             amount=to_real_coins(testnet, self.content.amount),
#         )

#     def to_real_msg_undelegate(self, testnet: Testnet):
#         return TerraStaking.MsgUndelegate(
#             delegator_address=testnet.acc_addr(self.signer),
#             validator_address=testnet.val_addr(self.content.validatorAddress, True),
#             amount=to_real_coins(testnet, self.content.amount),
#         )

#     def to_real_msg_redelegate(self, testnet: Testnet):
#         return TerraStaking.MsgBeginRedelegate(
#             delegator_address=testnet.acc_addr(self.signer),
#             validator_src_address=testnet.val_addr(
#                 self.content.validatorSrcAddress, True
#             ),
#             validator_dst_address=testnet.val_addr(
#                 self.content.validatorDstAddress, True
#             ),
#             amount=to_real_coins(testnet, self.content.amount),
#         )


# def sdk_msg_to_real(sdk_msg: SdkMsgs, testnet: Testnet):
#     match sdk_msg.content.typeUrl:
#         case "send":
#             return sdk_msg.to_real_msg_send(testnet)
#         case "delegate":
#             return sdk_msg.to_real_msg_delegate(testnet)
#         case "undelegate":
#             return sdk_msg.to_real_msg_undelegate(testnet)
#         case "redelegate":
#             return sdk_msg.to_real_msg_redelegate(testnet)
#         case _:
#             raise ValueError(f"message type not supported {sdk_msg.content.typeUrl}")


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


def get_grant(grantStore: GrantStore, grantId: GrantIds) -> Grant:
    for k, v in grantStore.items():
        if (
            k.grantee == grantId.grantee
            and k.granter == grantId.granter
            and k.msgTypeUrl == grantId.msgTypeUrl
        ):
            return v

    raise ("There is an error in the model!")


MsgResponseErrors = str


class Response:
    type: str
    ok: bool
    error: Optional[MsgResponseErrors]
