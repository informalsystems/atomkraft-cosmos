import logging
from munch import unmunchify
import time

from atomkraft.chain import Testnet
from atomkraft.chain.utils import TmEventSubscribe
from modelator.pytest.decorators import step

from terra_proto.cosmos.staking.v1beta1 import AuthorizationType as StakingAuthType
from terra_proto.cosmos.base.abci.v1beta1 import TxResponse
from terra_sdk.core.authz import (
    AuthorizationGrant,
    GenericAuthorization,
    MsgExecAuthorized,
    MsgGrantAuthorization,
    MsgRevokeAuthorization,
    SendAuthorization,
    StakeAuthorization,
)
from terra_sdk.core.authz.data import StakeAuthorizationValidators
from terra_sdk.core.bank import MsgSend
from terra_sdk.core.coin import Coin
from terra_sdk.core.staking import MsgBeginRedelegate, MsgDelegate, MsgUndelegate

from reactors import model_data as model

MSG_TYPE = {
    "msg_alpha": "msg_alpha",
    "send": MsgSend.type_url,
    "delegate": MsgDelegate.type_url,
    "undelegate": MsgUndelegate.type_url,
    "redelegate": MsgBeginRedelegate.type_url,
}

STAKING_AUTH_TYPE = {
    "delegate": StakingAuthType.AUTHORIZATION_TYPE_DELEGATE,
    "undelegate": StakingAuthType.AUTHORIZATION_TYPE_UNDELEGATE,
    "redelegate": StakingAuthType.AUTHORIZATION_TYPE_REDELEGATE,
    "msg_alpha": StakingAuthType.AUTHORIZATION_TYPE_UNSPECIFIED,
}


def to_real_coins(testnet: Testnet, coins: int):
    if coins == model.NO_MAX_COINS:
        return None

    # TODO: move to Testnet class
    return Coin.from_str(f"{int(coins)}{testnet.denom}")


# TODO: move to model.Grant class
def to_real_grant(
    testnet: Testnet,
    grant: model.Grant,
) -> AuthorizationGrant:
    authorization = to_real_auth(testnet, grant.authorization)
    logging.debug("🔹 authorization", authorization)
    expiration = model.to_real_time(grant.expirationTime)
    logging.debug("🔹 expiration", expiration)

    return AuthorizationGrant(authorization, expiration)


# TODO: move to model.Authorization class
def to_real_auth(testnet: Testnet, auth: model.Authorization):
    match auth.authorizationType:
        case "send":
            spend_limit = to_real_coins(testnet, auth.spendLimit)
            return SendAuthorization(spend_limit)

        case "delegate" | "undelegate" | "redelegate":
            authorization_type = STAKING_AUTH_TYPE[auth.authorizationType]
            logging.debug(f"🔸 auth_type {authorization_type}")

            max_tokens = to_real_coins(testnet, auth.maxTokens)

            addresses = [testnet.val_addr(address, True) for address in auth.validators]
            if auth.allow:
                allow_list = StakeAuthorizationValidators(addresses)
                deny_list = None
            else:
                allow_list = None
                deny_list = StakeAuthorizationValidators(addresses)
            logging.debug(f"🔸 allow_list {allow_list}")
            logging.debug(f"🔸 deny_list {deny_list}")

            return StakeAuthorization(
                authorization_type, max_tokens, allow_list, deny_list
            )

        case other:
            msg = MSG_TYPE[other]
            return GenericAuthorization(msg)


def show_result(result: TxResponse, expectedResponse: model.Response):
    if result.code == 0:
        logging.info("Status: Successful\n")
    else:
        logging.info("Status: Error")
        logging.info(f"\tcode: {result.code}")
        logging.info(f"\tlog:  {result.raw_log}\n")

    logging.debug("📌 result:", result)

    to_text = lambda ok: "OK" if ok else "FAIL"
    result_ok = result.code == 0
    logging.debug(
        f"📌 expected {to_text(expectedResponse.ok)}"
        f" (with error: {expectedResponse.error}), got {to_text(result_ok)}"
    )


@step("no-event")
def init(testnet: Testnet):
    logging.info("🔶 Step: init")

    logging.info(f"model accounts: {model.accounts}")
    logging.info(f"model validators: {model.validators}")

    testnet.set_accounts(model.accounts)
    testnet.set_validators(model.validators)
    testnet.verbose = True

    logging.info(f"Starting tesnet...")
    # testnet.oneshot()
    testnet.prepare()
    logging.info(f"..")
    testnet.spinup()
    logging.info(f"Waiting to be ready...")
    with TmEventSubscribe({"tm.event": "NewBlock"}):
        logging.info("Status: Testnet launched\n")


@step("request-grant")
def request_grant(
    testnet: Testnet,
    # event: model.MsgGrant,
    event: model.Event,
    expectedResponse: model.Response,
):
    logging.info("🔶 Step: request grant")
    assert event.type == "request-grant"

    granter = testnet.acc_addr(event.granter)
    grantee = testnet.acc_addr(event.grantee)
    logging.info(f"‣ granter: {event.granter} ({granter})")
    logging.info(f"‣ grantee: {event.grantee} ({grantee})")
    logging.info(f"‣ grant.authorization: {unmunchify(event.grant.authorization)}")
    logging.info(f"‣ grant.expirationTime: {event.grant.expirationTime}")

    grant = to_real_grant(testnet, event.grant)
    logging.debug(f"‣ grant: ${grant}")

    msg = MsgGrantAuthorization(granter, grantee, grant)
    logging.debug(f"‣ msg: ${msg}")

    result = testnet.broadcast_transaction(
        event.granter, msg, gas=200000, fee_amount=20000
    )
    show_result(result, expectedResponse)

    time.sleep(10)


@step("request-revoke")
def request_revoke(
    testnet: Testnet,
    # event: model.MsgRevoke,
    event: model.Event,
    expectedResponse: model.Response,
):
    logging.info("🔶 Step: revoke grant")
    assert event.type == "request-revoke"

    granter = testnet.acc_addr(event.granter)
    grantee = testnet.acc_addr(event.grantee)
    msg_type_url = MSG_TYPE[event.msgTypeUrl]
    logging.info(f"‣ granter: {event.granter} ({granter})")
    logging.info(f"‣ grantee: {event.grantee} ({grantee})")
    logging.info(f"‣ msgTypeUrl: {event.msgTypeUrl} ({msg_type_url})")

    msg = MsgRevokeAuthorization(granter, grantee, msg_type_url)
    logging.debug(f"‣ msg: ${msg}")

    result = testnet.broadcast_transaction(
        event.granter, msg, gas=200000, fee_amount=20000
    )

    show_result(result, expectedResponse)
    time.sleep(10)


@step("request-execute")
def request_execute(
    testnet: Testnet,
    # event: model.MsgExec,
    event: model.Event,
    expectedResponse: model.Response,
):
    logging.debug("🔶 Step: execute grant")
    assert event.type == "request-execute"

    grantee = testnet.acc_addr(event.grantee)
    logging.info(f"‣ grantee: {event.grantee} ({grantee})")

    # there's only one exec message in this model
    sdk_msg = event.msg
    logging.info(f"‣ sdk msg: {sdk_msg}")

    granter = testnet.acc_addr(sdk_msg.signer)
    logging.info(f"‣ sdk msg granter: {granter}")
    amount = to_real_coins(testnet, sdk_msg.content.amount)

    match sdk_msg.content.typeUrl:
        case "send":
            exec_msg = MsgSend(
                from_address=testnet.val_addr(event.msg.content.fromAddress, True),
                to_address=testnet.val_addr(event.msg.content.toAddress, True),
                amount=amount,
            )
        case "delegate":
            exec_msg = MsgDelegate(
                delegator_address=granter,
                validator_address=testnet.val_addr(
                    event.msg.content.validatorAddress, True
                ),
                amount=amount,
            )
        case "undelegate":
            exec_msg = MsgUndelegate(
                delegator_address=granter,
                validator_address=testnet.val_addr(
                    event.msg.content.validatorAddress, True
                ),
                amount=amount,
            )
        case "redelegate":
            exec_msg = MsgBeginRedelegate(
                delegator_address=granter,
                validator_src_address=testnet.val_addr(
                    event.msg.content.validatorSrcAddress, True
                ),
                validator_dst_address=testnet.val_addr(
                    event.msg.content.validatorDstAddress, True
                ),
                amount=amount,
            )
        case "msg_alpha":
            # TODO: ??
            pass

    msg = MsgExecAuthorized(grantee=grantee, msgs=[exec_msg])
    logging.debug(f"‣ msg: ${msg}")

    result = testnet.broadcast_transaction(
        sdk_msg.signer, msg, gas=200000, fee_amount=20000
    )
    show_result(result, expectedResponse)

    time.sleep(10)


@step("expire")
def expire(
    testnet: Testnet,
    # event: model.ExpireEvent,
    event: model.Event,
    grantStore: model.GrantStore,
    expectedResponse: model.Response,
):
    logging.info("🔶 Step: expire grant")
    assert event.type == "expire"

    granter = testnet.acc_addr(event.grantId.granter)
    grantee = testnet.acc_addr(event.grantId.grantee)
    msg_type_url = MSG_TYPE[event.grantId.msgTypeUrl]
    logging.info(f"‣ granter: {event.grantId.granter} ({granter})")
    logging.info(f"‣ grantee: {event.grantId.grantee} ({grantee})")
    logging.info(f"‣ msgTypeUrl: {event.grantId.msgTypeUrl} ({msg_type_url})")

    grant = model.get_grant(grantStore, event.grantId)
    if grant.expirationTime != "none":
        grant.expirationTime = model.ExpirationTime.expire_soon.name
    logging.info(f"‣ grant': {grant}")

    msg = MsgGrantAuthorization(granter, grantee, grant)
    logging.debug(f"‣ msg: ${msg}")

    result = testnet.broadcast_transaction(
        event.grantId.granter, msg, gas=200000, fee_amount=20000
    )
    show_result(result, expectedResponse)

    time.sleep(10)
    # this sleep is to wait for the grant expiration
    time.sleep(5)
