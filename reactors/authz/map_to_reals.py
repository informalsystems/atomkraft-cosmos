from argparse import ArgumentError
from datetime import datetime, timedelta
import logging
from typing import List
from atomkraft.chain import Testnet
from reactors.authz import model_data as model

from terra_proto.cosmos.staking.v1beta1 import AuthorizationType as StakingAuthType
from terra_sdk.core import authz as terra, staking, bank
from terra_sdk.core.coin import Coin
from terra_sdk.core.coins import Coins
from terra_sdk.core.msg import Msg as TerraMsg
from terra_sdk.util.converter import to_isoformat

def to_real_time(expiration_time: model.ExpirationTime):
    match expiration_time:
        case "past":
            return to_isoformat(datetime.now() - timedelta(seconds=100))
        case "future":
            return to_isoformat(datetime.now() + timedelta(seconds=100))
        case "expire_soon":
            return to_isoformat(datetime.now() + timedelta(seconds=model.EXPIRES_SOON_TIME))
        case "none":
            # terra.py client requires a concrete timestamp
            return to_isoformat(datetime.now() + timedelta(seconds=10000))


MSG_TYPE = {
    "msg_alpha": "msg_alpha",
    "send": bank.MsgSend.type_url,
    "delegate": staking.MsgDelegate.type_url,
    "undelegate": staking.MsgUndelegate.type_url,
    "redelegate": staking.MsgBeginRedelegate.type_url,
}

# STAKING_AUTH_TYPE = {
#     MsgTypeUrls.delegate: TerraStakingAuthType.AUTHORIZATION_TYPE_DELEGATE,
#     MsgTypeUrls.undelegate: TerraStakingAuthType.AUTHORIZATION_TYPE_UNDELEGATE,
#     MsgTypeUrls.redelegate: TerraStakingAuthType.AUTHORIZATION_TYPE_REDELEGATE,
#     MsgTypeUrls.generic: TerraStakingAuthType.AUTHORIZATION_TYPE_UNSPECIFIED,
# }

STAKING_AUTH_TYPE = {
    "delegate": StakingAuthType.AUTHORIZATION_TYPE_DELEGATE,
    "undelegate": StakingAuthType.AUTHORIZATION_TYPE_UNDELEGATE,
    "redelegate": StakingAuthType.AUTHORIZATION_TYPE_REDELEGATE,
    "msg_alpha": StakingAuthType.AUTHORIZATION_TYPE_UNSPECIFIED,
}


def to_real_coin(testnet: Testnet, coins: int):
    if coins == model.NO_MAX_COINS:
        return None

    # TODO: move to Testnet class
    return Coin.from_str(f"{int(coins)}{testnet.denom}")

def to_real_coins(testnet: Testnet, coins: List[int]):
    if len(coins) != 1:
        raise ArgumentError("Currently only accept one coin value.")
    coins = coins[0]
    
    if coins == model.NO_MAX_COINS:
        return None

    # TODO: move to Testnet class
    return Coins.from_str(f"{int(coins)}{testnet.denom}")


# TODO: move to model.Grant class
def to_real_grant(
    testnet: Testnet,
    grant: model.Grant,
):
    return terra.AuthorizationGrant(
        authorization=to_real_auth(testnet, grant.authorization),
        expiration=to_real_time(grant.expirationTime),
    )


def to_real_generic_auth(auth: model.GenericAuthorization):
    logging.debug("to_real_generic_auth")
    return terra.GenericAuthorization(msg=MSG_TYPE[auth.msgTypeUrl])


def to_real_send_auth(testnet: Testnet, auth: model.SendAuthorization):
    return terra.SendAuthorization(spend_limit=to_real_coins(testnet, [auth.spendLimit]))


def to_real_stake_auth(testnet: Testnet, auth: model.StakeAuthorization):
    validators = to_real_validators(testnet, auth.validators)
    return terra.StakeAuthorization(
        authorization_type=STAKING_AUTH_TYPE[auth.msgTypeUrl],
        max_tokens=to_real_coin(testnet, auth.maxTokens),
        allow_list=validators if auth.allow else None,
        deny_list=validators if not auth.allow else None,
    )


def to_real_validators(testnet: Testnet, validators: model.Validators):
    addresses = [testnet.val_addr(address, True) for address in validators]
    return terra.data.StakeAuthorizationValidators(addresses)


# TODO: move to model.Authorization class
def to_real_auth(testnet: Testnet, auth: model.Authorization):
    match auth.msgTypeUrl:
        case "send":
            if 'spendLimit' in auth:
                return to_real_send_auth(testnet, auth)
            else:
                return to_real_generic_auth(auth)
        case "delegate" | "undelegate" | "redelegate":
            if 'validators' in auth:
                return to_real_stake_auth(testnet, auth)
            else:
                return to_real_generic_auth(auth)
        case "generic":
            return to_real_generic_auth(auth)


def to_real_msg_send(testnet: Testnet, msg: model.SdkMsgs):
    return bank.MsgSend(
        from_address=testnet.acc_addr(msg.content.fromAddress),
        to_address=testnet.acc_addr(msg.content.toAddress),
        amount=to_real_coins(testnet, [msg.content.amount]),
    )


def to_real_msg_delegate(testnet: Testnet, msg: model.SdkMsgs):
    return staking.MsgDelegate(
        delegator_address=testnet.acc_addr(msg.signer),
        validator_address=testnet.val_addr(msg.content.validatorAddress, True),
        amount=to_real_coin(testnet, msg.content.amount),
    )


def to_real_msg_undelegate(testnet: Testnet, msg: model.SdkMsgs):
    return staking.MsgUndelegate(
        delegator_address=testnet.acc_addr(msg.signer),
        validator_address=testnet.val_addr(msg.content.validatorAddress, True),
        amount=to_real_coin(testnet, msg.content.amount),
    )


def to_real_msg_redelegate(testnet: Testnet, msg: model.SdkMsgs):
    return staking.MsgBeginRedelegate(
        delegator_address=testnet.acc_addr(msg.signer),
        validator_src_address=testnet.val_addr(msg.content.validatorSrcAddress, True),
        validator_dst_address=testnet.val_addr(msg.content.validatorDstAddress, True),
        amount=to_real_coin(testnet, msg.content.amount),
    )


def to_real_exec_msg(testnet: Testnet, sdk_msg: model.SdkMsgs) -> TerraMsg:
    match sdk_msg.content.typeUrl:
        case "send":
            return to_real_msg_send(testnet, sdk_msg)
        case "delegate":
            return to_real_msg_delegate(testnet, sdk_msg)
        case "undelegate":
            return to_real_msg_undelegate(testnet, sdk_msg)
        case "redelegate":
            return to_real_msg_redelegate(testnet, sdk_msg)
        case _:
            # raise ValueError(f"message type not supported {sdk_msg.content.typeUrl}")
            return None
