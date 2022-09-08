import logging
from munch import unmunchify
import time
from timeit import default_timer as timer

from atomkraft.chain import Testnet
from atomkraft.chain.utils import TmEventSubscribe
from modelator.pytest.decorators import step

from reactors import model_data as model
from .map_to_reals import to_real_grant, MSG_TYPE, to_real_exec_msg

from terra_proto.cosmos.base.abci.v1beta1 import TxResponse
from terra_sdk.core.authz import (
    MsgExecAuthorized,
    MsgGrantAuthorization,
    MsgRevokeAuthorization,
)


def show_result(result: TxResponse, expectedResponse: model.Response):
    if result.code == 0:
        logging.info(f"Status: Successful")
    else:
        logging.info("Status: Error")
        logging.info(f"\tcode: {result.code}")
        logging.info(f"\tlog:  {result.raw_log}\n")

    to_text = lambda ok: "OK" if ok else "FAIL"
    logging.info(
        f"Expected {to_text(expectedResponse.ok)}, "
        f"with error: {expectedResponse.error}\n"
    )


def check_result(result: TxResponse, expectedResponse: model.Response):
    assert (result.code == 0) == expectedResponse.ok


WAIT_TIME = 0


@step("no-event")
def init(testnet: Testnet):
    logging.info("🔶 Step: init")

    logging.info(f"model accounts: {model.accounts}")
    logging.info(f"model validators: {model.validators}")

    testnet.set_accounts(model.accounts)
    testnet.set_validators(model.validators)
    testnet.verbose = True

    # testnet.oneshot()
    logging.info(f"Preparing testnet...")
    start_time = timer()
    testnet.prepare()
    logging.info(f"Prapare time: {(timer() - start_time):.2f} seconds")

    logging.info(f"Spinup testnet...")
    start_time = timer()
    testnet.spinup()
    logging.info(f"Spinup time: {(timer() - start_time):.2f} seconds")

    logging.info(f"Wait for testnet to be ready...")
    start_time = timer()
    with TmEventSubscribe({"tm.event": "NewBlock"}):
        logging.info(f"Waiting time: {(timer() - start_time):.2f} seconds")
        logging.info("Testnet launched! 🚀\n")


@step("request-grant")
def request_grant(
    testnet: Testnet,
    event: model.MsgGrant,
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
    check_result(result, expectedResponse)

    time.sleep(WAIT_TIME)


@step("request-revoke")
def request_revoke(
    testnet: Testnet,
    event: model.MsgRevoke,
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
    check_result(result, expectedResponse)

    time.sleep(WAIT_TIME)


@step("request-execute")
def request_execute(
    testnet: Testnet,
    event: model.MsgExec,
    expectedResponse: model.Response,
):
    logging.info("🔶 Step: execute grant")
    assert event.type == "request-execute"

    grantee = testnet.acc_addr(event.grantee)
    logging.info(f"‣ grantee: {event.grantee} ({grantee})")

    # there's only one exec message in this model
    sdk_msg = event.msg
    logging.info(f"‣ sdk msg: {unmunchify(sdk_msg)}")

    exec_msg = to_real_exec_msg(testnet, sdk_msg)
    logging.info(f"‣ exec_msg: ${exec_msg}")
    msg = MsgExecAuthorized(grantee=grantee, msgs=[exec_msg])
    logging.info(f"‣ msg: ${msg}")

    result = testnet.broadcast_transaction(
        sdk_msg.signer, msg, gas=200000, fee_amount=20000
    )
    show_result(result, expectedResponse)
    check_result(result, expectedResponse)

    time.sleep(WAIT_TIME)


@step("expire")
def expire(
    testnet: Testnet,
    event: model.ExpireEvent,
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

    model_grant = model.get_grant(grantStore, event.grantId)
    if model_grant.expirationTime != "none":
        model_grant.expirationTime = model.ExpirationTime.expire_soon.name
    logging.info(f"‣ grant': {model_grant}")
    grant = to_real_grant(testnet, model_grant)

    msg = MsgGrantAuthorization(granter, grantee, grant)
    logging.debug(f"‣ msg: ${msg}")

    result = testnet.broadcast_transaction(
        event.grantId.granter, msg, gas=200000, fee_amount=20000
    )
    show_result(result, expectedResponse)
    check_result(result, expectedResponse)

    time.sleep(WAIT_TIME)

    # this sleep is to wait for the grant expiration
    time.sleep(model.EXPIRES_SOON_TIME)
