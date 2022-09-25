from datetime import datetime, timedelta
from enum import Enum, unique
import logging
from typing import Literal, Optional, Union

from atomkraft.chain import Testnet
from terra_proto.cosmos.staking.v1beta1 import AuthorizationType as StakingAuthType
from terra_sdk.core import authz as terra, staking, bank
from terra_sdk.core.coin import Coin as TerraCoin
from terra_sdk.core.coins import Coins as TerraCoins
from terra_sdk.core.msg import Msg as TerraMsg
from terra_sdk.util.converter import to_isoformat
from terra_sdk.core.authz import (
    MsgExecAuthorized,
    MsgGrantAuthorization,
    MsgRevokeAuthorization,
)

accounts = ["a1", "a2", "a3"]
validators = ["v1", "v2", "v3"]

NO_MAX_COINS = -99

################################################################################

AccAddress = str
ValAddress = str
Coins = int

################################################################################


def to_real_coin(testnet: Testnet, coins: int):
    if coins == NO_MAX_COINS:
        return None

    return TerraCoin.from_str(f"{int(coins)}{testnet.denom}")


def to_real_coins(testnet: Testnet, coins: list[int]):
    if len(coins) != 1:
        raise ValueError("Currently only accept one coin value.")
    coins = coins[0]

    if coins == NO_MAX_COINS:
        return None

    return TerraCoins.from_str(f"{int(coins)}{testnet.denom}")


################################################################################


class ModelObject:
    def __init__(self, *args, **kwargs):
        if args and len(args) > 0 and isinstance(args[0], dict):
            for varname, expected_type in self.__annotations__.items():
                self._assign_type(varname, expected_type, args[0])
        else:
            self.__dict__.update(kwargs)

    def _assign_type(self, var_name, expected_type, var_values):
        if var_name not in var_values:
            raise TypeError(f"Field '{var_name}' not in {var_values}")
        elif expected_type.__class__.__name__ == "EnumMeta":
            setattr(
                self, var_name, eval(f"{expected_type.__name__}.{var_values[var_name]}")
            )
        elif expected_type.__name__ == "Literal":
            if var_values[var_name] in expected_type.__args__:
                setattr(self, var_name, var_values[var_name])
            else:
                raise TypeError(
                    f"Could not find a matching type for {var_name}={var_values[var_name]} in {expected_type}"
                )
        elif expected_type.__name__ == "Union":
            for t in expected_type.__args__:
                try:
                    self._assign_type(var_name, t, var_values)
                    return
                except:
                    pass
            raise TypeError(
                f"Could not find a matching type for {var_name}={var_values[var_name]} in {expected_type.__args__}"
            )
        elif isinstance(var_values[var_name], (int, str)):
            setattr(self, var_name, var_values[var_name])
        else:
            setattr(
                self,
                var_name,
                eval(f"{expected_type.__name__}({var_values[var_name]})"),
            )


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

EXPIRES_SOON_TIME = 2


class ExpirationTime(Enum):
    past = 1
    future = 2
    none = 3
    expire_soon = 4

    def to_real(self):
        match self:
            case self.past:
                return to_isoformat(datetime.now() - timedelta(seconds=100))
            case self.future:
                return to_isoformat(datetime.now() + timedelta(seconds=100))
            case self.none:
                # terra.py client requires a concrete timestamp
                return to_isoformat(datetime.now() + timedelta(seconds=10000))
            case self.expire_soon:
                return to_isoformat(
                    datetime.now() + timedelta(seconds=EXPIRES_SOON_TIME)
                )


################################################################################


class Authorization(ModelObject):
    type: Literal["generic-authorization", "send-authorization", "stake-authorization"]
    msgTypeUrl: MsgTypeUrls


################################################################################


class GenericAuthorization(Authorization):
    type: Literal["generic-authorization"]
    msgTypeUrl: MsgTypeUrls

    def to_real(self, _testnet: Testnet):
        return terra.GenericAuthorization(msg=self.msgTypeUrl.to_real())


################################################################################
class SendAuthorization(Authorization):
    type: Literal["send-authorization"]
    msgTypeUrl: MsgTypeUrls
    spendLimit: Coins
    allowList: list[ValAddress]

    def to_real(self, testnet: Testnet):
        return terra.SendAuthorization(
            spend_limit=to_real_coins(testnet, [self.spendLimit])
            # FIX: terra library does not support `allow_list``
        )


class MsgSend(ModelObject):
    signer: AccAddress
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


class MsgDelegate(ModelObject):
    signer: AccAddress
    typeUrl: Literal["delegate"]
    delegatorAddress: AccAddress
    validatorAddress: ValAddress
    amount: Coins

    def to_real(self, testnet: Testnet) -> TerraMsg:
        return staking.MsgDelegate(
            delegator_address=testnet.acc_addr(self.signer),
            validator_address=testnet.val_addr(self.validatorAddress, True),
            amount=to_real_coin(testnet, self.amount),
        )


class MsgUndelegate(ModelObject):
    signer: AccAddress
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


class MsgBeginRedelegate(ModelObject):
    signer: AccAddress
    typeUrl: Literal["redelegate"]
    delegatorAddress: AccAddress
    validatorSrcAddress: ValAddress
    validatorDstAddress: ValAddress
    amount: Coins

    def to_real(self, testnet: Testnet) -> TerraMsg:
        return staking.MsgBeginRedelegate(
            delegator_address=testnet.acc_addr(self.signer),
            validator_src_address=testnet.val_addr(self.validatorSrcAddress, True),
            validator_dst_address=testnet.val_addr(self.validatorDstAddress, True),
            amount=to_real_coin(testnet, self.amount),
        )


################################################################################


class Grant(ModelObject):
    authorization: Union[GenericAuthorization, SendAuthorization, StakeAuthorization]
    expiration: ExpirationTime

    def to_real(self, testnet: Testnet):
        return terra.AuthorizationGrant(
            authorization=self.authorization.to_real(testnet),
            expiration=self.expiration.to_real(),
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
        logging.info(f"‣ granter: {self.granter} ({granter})")

        grantee = testnet.acc_addr(self.grantee)
        logging.info(f"‣ grantee: {self.grantee} ({grantee})")

        grant = self.grant.to_real(testnet)
        logging.debug(f"‣ grant: {grant}")

        return MsgGrantAuthorization(granter, grantee, grant)


class MsgRevoke(ModelObject):
    type: Literal["request-revoke"]
    granter: AccAddress
    grantee: AccAddress
    msgTypeUrl: MsgTypeUrls

    def to_real(self, testnet: Testnet):
        granter = testnet.acc_addr(self.granter)
        logging.info(f"‣ granter: {self.granter} ({granter})")

        grantee = testnet.acc_addr(self.grantee)
        logging.info(f"‣ grantee: {self.grantee} ({grantee})")

        msg_type_url = self.msgTypeUrl.to_real()
        logging.info(f"‣ msgTypeUrl: {self.msgTypeUrl} ({msg_type_url})")

        return MsgRevokeAuthorization(granter, grantee, msg_type_url)


class MsgExec(ModelObject):
    type: Literal["request-execute"]
    grantee: AccAddress
    msg: Union[MsgSend, MsgDelegate, MsgUndelegate, MsgBeginRedelegate]

    def to_real(self, testnet: Testnet):
        grantee = testnet.acc_addr(self.grantee)
        logging.info(f"‣ grantee: {self.grantee} ({grantee})")

        # the current model allows only one exec message
        msg = self.msg.to_real(testnet)
        logging.info(f"‣ real msg: {msg}")

        return MsgExecAuthorized(grantee=grantee, msgs=[msg])


################################################################################


class ExpireEvent(ModelObject):
    type: Literal["expire"]
    grantId: GrantIds


Event = Union[MsgGrant, MsgRevoke, MsgExec, ExpireEvent]

################################################################################


class Response(ModelObject):
    type: Literal[
        "no-response", "response-grant", "response-revoke", "response-execute"
    ]
    ok: bool
    error: Literal[
        "none",
        "granter-equal-grantee",
        "authorization-expired",
        "grant-not-found",
        "authorization-expired",
        "insufficient-amount",
        "account-not-allowed",
        "validator-not-allowed",
        "validator-denied",
    ]


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
