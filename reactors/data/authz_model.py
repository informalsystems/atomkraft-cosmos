from datetime import datetime, timedelta
from enum import Enum, unique
from typing import Literal, Optional, Union

from atomkraft.chain import Testnet
from terra_proto.cosmos.staking.v1beta1 import AuthorizationType as StakingAuthType  # type: ignore
from terra_sdk.core import authz as terra, staking, bank  # type: ignore
from terra_sdk.core.coin import Coin as TerraCoin  # type: ignore
from terra_sdk.core.coins import Coins as TerraCoins  # type: ignore
from terra_sdk.core.msg import Msg as TerraMsg  # type: ignore
from terra_sdk.util.converter import to_isoformat  # type: ignore
from terra_sdk.core.authz import (  # type: ignore
    MsgExecAuthorized,
    MsgGrantAuthorization,
    MsgRevokeAuthorization,
)

from reactors.authz import logger

################################################################################


class ModelObject:
    def __init__(self, *args, **kwargs):
        """Initialize object from a dictionary and recursively create instances of nested ModelObjects"""
        if args and len(args) > 0 and isinstance(args[0], dict):
            for var_name, expected_type in self.__annotations__.items():
                self._assign_type(var_name, expected_type, args[0])
        else:
            self.__dict__.update(kwargs)

    def _assign_type(self, var_name, type_annotation, values):
        if var_name not in values:
            raise TypeError(f"Field '{var_name}' not in {values}")
        value = values[var_name]

        expected_type = type_annotation.__name__
        if type_annotation.__class__.__name__ == "EnumMeta":
            # Try to instantiate var_name as an enum type
            setattr(self, var_name, eval(f"{expected_type}.{value}"))
        elif expected_type == "Literal":
            # Try to instantiate var_name as one of the strings in the Literal type.
            if value in type_annotation.__args__:
                setattr(self, var_name, value)
            else:
                raise TypeError(
                    f"Could not find a matching type for {var_name}={value} in {type_annotation}"
                )
        elif expected_type == "Union":
            # Try to instantiate var_name as one of the types of the union.
            for t in type_annotation.__args__:
                try:
                    self._assign_type(var_name, t, values)
                    return
                except:
                    pass
            raise TypeError(
                f"Could not find a matching type for {var_name}={value} in {type_annotation.__args__}"
            )
        elif isinstance(value, (int, str)):
            setattr(self, var_name, value)
        else:
            # Instantiate var_name with a class of expected_type
            setattr(self, var_name, eval(f"{expected_type}({value})"))


################################################################################

NO_MAX_COINS = -99

AccAddress = str
ValAddress = str
Coins = int

################################################################################


def to_real_coin(testnet: Testnet, coins: Optional[int]):
    if coins is None or coins == NO_MAX_COINS:
        return None

    return TerraCoin.from_str(f"{int(coins)}{testnet.denom}")


def to_real_coins(testnet: Testnet, coin_list: list[int]):
    if len(coin_list) != 1:
        raise ValueError("Currently only accept one coin value.")
    coins = coin_list[0]

    if coins == NO_MAX_COINS:
        return None

    return TerraCoins.from_str(f"{int(coins)}{testnet.denom}")


################################################################################


@unique
class MsgTypeUrls(Enum):
    generic = 1
    send = 2
    delegate = 3
    undelegate = 4
    redelegate = 5

    def to_real(self):
        match self:
            case self.generic:
                raise ValueError("generic not allowed")
            case self.send:
                return bank.MsgSend.type_url
            case self.delegate:
                return staking.MsgDelegate.type_url
            case self.undelegate:
                return staking.MsgUndelegate.type_url
            case self.redelegate:
                return staking.MsgBeginRedelegate.type_url


################################################################################

EXPIRES_SOON_TIME = 10  # seconds to expire after 'now'


class ExpirationTime(Enum):
    past = 1
    future = 2
    none = 3
    expire_soon = 4

    def to_real(self):
        match self:
            case self.past:
                return to_isoformat(datetime.now() - timedelta(seconds=60))
            case self.future:
                return to_isoformat(datetime.now() + timedelta(seconds=60))
            case self.none:
                # terra.py client requires a concrete timestamp
                return to_isoformat(datetime.now() + timedelta(seconds=3600))
            case self.expire_soon:
                return to_isoformat(
                    datetime.now() + timedelta(seconds=EXPIRES_SOON_TIME)
                )


################################################################################


class Authorization(ModelObject):
    type: Literal["generic-authorization", "send-authorization", "stake-authorization"]
    msgTypeUrl: MsgTypeUrls

    def __repr__(self) -> str:
        return f"Authorization(type: {self.type}, msgTypeUrl: {self.msgTypeUrl})"


################################################################################


class GenericAuthorization(Authorization):
    type: Literal["generic-authorization"]
    msgTypeUrl: MsgTypeUrls

    def to_real(self, _testnet: Testnet):
        return terra.GenericAuthorization(msg=self.msgTypeUrl.to_real())

    def __repr__(self) -> str:
        return f"GenericAuthorization(msgTypeUrl: {self.msgTypeUrl})"


################################################################################
class SendAuthorization(Authorization):
    type: Literal["send-authorization"]
    msgTypeUrl: MsgTypeUrls
    spendLimit: Coins
    allowList: list[ValAddress]

    def to_real(self, testnet: Testnet):
        return terra.SendAuthorization(
            spend_limit=to_real_coins(testnet, [self.spendLimit])
            # FIX: terra library does not support `allow_list`
        )

    def __repr__(self) -> str:
        return f"SendAuthorization(msgTypeUrl: {self.msgTypeUrl}, spendLimit: {self.spendLimit}, allowList: {self.allowList})"


class MsgSend(ModelObject):
    typeUrl: Literal["send"]
    fromAddress: AccAddress
    toAddress: AccAddress
    amount: Coins

    def to_real(self, testnet: Testnet) -> TerraMsg:
        return bank.MsgSend(
            from_address=testnet.acc_addr(self.fromAddress),
            to_address=testnet.acc_addr(self.toAddress),
            amount=to_real_coins(testnet, [self.amount]),
        )

    def __repr__(self) -> str:
        return f"MsgSend(typeUrl: {self.typeUrl}, from_address: {self.fromAddress}, toAddress: {self.toAddress}, amount: {self.amount})"


################################################################################

Validators = list[ValAddress]


def to_real_validators(testnet: Testnet, validators: Validators):
    addresses = [testnet.val_addr(address, True) for address in validators]
    return terra.data.StakeAuthorizationValidators(addresses)


STAKING_AUTH_TYPE = {
    "delegate": StakingAuthType.AUTHORIZATION_TYPE_DELEGATE,
    "undelegate": StakingAuthType.AUTHORIZATION_TYPE_UNDELEGATE,
    "redelegate": StakingAuthType.AUTHORIZATION_TYPE_REDELEGATE,
    "msg_alpha": StakingAuthType.AUTHORIZATION_TYPE_UNSPECIFIED,
}


class StakeAuthorization(Authorization):
    type: Literal["stake-authorization"]
    msgTypeUrl: MsgTypeUrls
    maxTokens: Optional[Coins]
    validators: Validators
    allow: bool

    def to_real(self, testnet: Testnet):
        validators = to_real_validators(testnet, self.validators)
        return terra.StakeAuthorization(
            authorization_type=STAKING_AUTH_TYPE[self.msgTypeUrl.name],
            max_tokens=to_real_coin(testnet, self.maxTokens),
            allow_list=validators if self.allow else None,
            deny_list=validators if not self.allow else None,
        )

    def __repr__(self) -> str:
        return f"StakeAuthorization(msgTypeUrl: {self.msgTypeUrl}, maxTokens: {self.maxTokens}, validators: {self.validators}, allow: {self.allow})"


class MsgDelegate(ModelObject):
    typeUrl: Literal["delegate"]
    delegatorAddress: AccAddress
    validatorAddress: ValAddress
    amount: Coins

    def to_real(self, testnet: Testnet) -> TerraMsg:
        return staking.MsgDelegate(
            delegator_address=testnet.acc_addr(self.delegatorAddress),
            validator_address=testnet.val_addr(self.validatorAddress, True),
            amount=to_real_coin(testnet, self.amount),
        )

    def __repr__(self) -> str:
        return f"MsgDelegate(typeUrl: {self.typeUrl}, delegatorAddress: {self.delegatorAddress}, validatorAddress: {self.validatorAddress}, amount: {self.amount})"


class MsgUndelegate(ModelObject):
    typeUrl: Literal["undelegate"]
    delegatorAddress: AccAddress
    validatorAddress: ValAddress
    amount: Coins

    def to_real(self, testnet: Testnet) -> TerraMsg:
        return staking.MsgUndelegate(
            delegator_address=testnet.acc_addr(self.delegatorAddress),
            validator_address=testnet.val_addr(self.validatorAddress, True),
            amount=to_real_coin(testnet, self.amount),
        )

    def __repr__(self) -> str:
        return f"MsgUndelegate(typeUrl: {self.typeUrl}, delegatorAddress: {self.delegatorAddress}, validatorAddress: {self.validatorAddress}, amount: {self.amount})"


class MsgBeginRedelegate(ModelObject):
    typeUrl: Literal["redelegate"]
    delegatorAddress: AccAddress
    validatorSrcAddress: ValAddress
    validatorDstAddress: ValAddress
    amount: Coins

    def to_real(self, testnet: Testnet) -> TerraMsg:
        return staking.MsgBeginRedelegate(
            delegator_address=testnet.acc_addr(self.delegatorAddress),
            validator_src_address=testnet.val_addr(self.validatorSrcAddress, True),
            validator_dst_address=testnet.val_addr(self.validatorDstAddress, True),
            amount=to_real_coin(testnet, self.amount),
        )

    def __repr__(self) -> str:
        return f"MsgBeginRedelegate(typeUrl: {self.typeUrl}, delegatorAddress: {self.delegatorAddress}, validatorSrcAddress: {self.validatorSrcAddress}, validatorDstAddress: {self.validatorDstAddress}, amount: {self.amount})"


################################################################################


class Grant(ModelObject):
    authorization: Union[GenericAuthorization, SendAuthorization, StakeAuthorization]
    expiration: ExpirationTime

    def to_real(self, testnet: Testnet):
        return terra.AuthorizationGrant(
            authorization=self.authorization.to_real(testnet),
            expiration=self.expiration.to_real(),
        )

    def __repr__(self) -> str:
        return (
            f"Grant(authorization: {self.authorization}, expiration: {self.expiration})"
        )


################################################################################
class GrantIds(ModelObject):
    granter: AccAddress
    grantee: AccAddress
    msgTypeUrl: MsgTypeUrls


class MsgGrant(ModelObject):
    type: Literal["request-grant"]
    granter: AccAddress
    grantee: AccAddress
    grant: Grant

    def to_real(self, testnet: Testnet):
        granter = testnet.acc_addr(self.granter)
        logger.debug(f"??? granter: {self.granter} ({granter})")

        grantee = testnet.acc_addr(self.grantee)
        logger.debug(f"??? grantee: {self.grantee} ({grantee})")

        grant = self.grant.to_real(testnet)
        logger.debug(f"??? grant: {grant}")

        return MsgGrantAuthorization(granter, grantee, grant)

    def __repr__(self) -> str:
        return f"MsgGrant(granter: {self.granter}, grantee: {self.grantee}, msg: {self.grant})"


class MsgRevoke(ModelObject):
    type: Literal["request-revoke"]
    granter: AccAddress
    grantee: AccAddress
    msgTypeUrl: MsgTypeUrls

    def to_real(self, testnet: Testnet):
        granter = testnet.acc_addr(self.granter)
        logger.debug(f"??? granter: {self.granter} ({granter})")

        grantee = testnet.acc_addr(self.grantee)
        logger.debug(f"??? grantee: {self.grantee} ({grantee})")

        msg_type_url = self.msgTypeUrl.to_real()
        logger.debug(f"??? msgTypeUrl: {self.msgTypeUrl} ({msg_type_url})")

        return MsgRevokeAuthorization(granter, grantee, msg_type_url)

    def __repr__(self) -> str:
        return f"MsgRevoke(granter: {self.granter}, grantee: {self.grantee}, msgTypeUrl: {self.msgTypeUrl})"


class MsgExec(ModelObject):
    type: Literal["request-execute"]
    grantee: AccAddress
    msg: Union[MsgSend, MsgDelegate, MsgUndelegate, MsgBeginRedelegate]

    def to_real(self, testnet: Testnet):
        grantee = testnet.acc_addr(self.grantee)
        logger.debug(f"??? grantee: {self.grantee} ({grantee})")

        # the current model allows only one exec message
        msg = self.msg.to_real(testnet)
        logger.debug(f"??? real msg: {msg}")

        return MsgExecAuthorized(grantee=grantee, msgs=[msg])

    def __repr__(self) -> str:
        return f"MsgExec(grantee: {self.grantee}, msg: {self.msg})"


################################################################################


class ExpireEvent(ModelObject):
    type: Literal["expire"]
    grantId: GrantIds
    authorization: Authorization


Event = Union[MsgGrant, MsgRevoke, MsgExec, ExpireEvent]

################################################################################


class Response(ModelObject):
    type: Literal[
        "no-response", "response-grant", "response-revoke", "response-execute"
    ]
    ok: bool
    error: str


################################################################################

GrantStore = dict[GrantIds, Grant]


def get_grant(grantStore: GrantStore, grantId: GrantIds) -> Grant:
    for k, v in grantStore.items():
        if (
            k.grantee == grantId.grantee
            and k.granter == grantId.granter
            and k.msgTypeUrl == grantId.msgTypeUrl
        ):
            return v

    raise ValueError("There is an error in the model!")
