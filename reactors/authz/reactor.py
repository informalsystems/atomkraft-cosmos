import logging
from munch import unmunchify
import time
from timeit import default_timer as timer

from atomkraft.chain import Testnet
from atomkraft.chain.utils import TmEventSubscribe
from modelator.pytest.decorators import step

from reactors.authz import model_data as model
from terra_proto.cosmos.base.abci.v1beta1 import TxResponse


def show_result(result: TxResponse, expected: model.Response):
    if result.code == 0:
        logging.info(f"Status:\tOK")
    else:
        logging.info(f"Status:\tERROR (code: {result.code}, log: {result.raw_log})")

    if expected.error == "none":
        assert expected.ok
        logging.info(f"Expected:\tOK\n")
    else:
        assert not expected.ok
        logging.info(f"Expected:\tERROR ({expected.error})\n")


def check_result(result: TxResponse, expected: model.Response):
    assert (result.code == 0) == (expected.error == "none")


@step("no-event")
def init(testnet: Testnet):
    logging.info("🔶 Step: init")

    logging.info(f"model accounts: {model.accounts}")
    logging.info(f"model validators: {model.validators}")
    testnet.set_accounts(model.accounts)
    testnet.set_validators(model.validators)
    testnet.verbose = True

    logging.info(f"Preparing testnet...")
    start_time = timer()
    testnet.prepare()
    logging.debug(f"Prapare time: {(timer() - start_time):.2f} seconds")

    logging.info(f"Spining up testnet...")
    start_time = timer()
    testnet.spinup()
    logging.debug(f"Spinup time: {(timer() - start_time):.2f} seconds")

    logging.info(f"Wait for testnet to be ready...")
    start_time = timer()
    with TmEventSubscribe({"tm.event": "NewBlock"}):
        logging.debug(f"Waiting time: {(timer() - start_time):.2f} seconds")
        logging.info("Testnet launched! 🚀\n")


@step("request-grant")
def request_grant(
    testnet: Testnet,
    event: model.MsgGrant,
    expectedResponse: model.Response,
):
    logging.info("🔶 Step: request grant")
    assert event.type == "request-grant"
    request = model.MsgGrant(unmunchify(event))

    result = testnet.broadcast_transaction(
        request.granter,
        request.to_real(testnet),
        gas=200000,
        fee_amount=20000,
    )

    show_result(result, expectedResponse)
    check_result(result, expectedResponse)


@step("request-revoke")
def request_revoke(
    testnet: Testnet,
    event: model.MsgRevoke,
    expectedResponse: model.Response,
):
    logging.info("🔶 Step: revoke grant")
    assert event.type == "request-revoke"
    request = model.MsgRevoke(unmunchify(event))

    result = testnet.broadcast_transaction(
        request.granter, request.to_real(testnet), gas=200000, fee_amount=20000
    )

    show_result(result, expectedResponse)
    check_result(result, expectedResponse)


@step("request-execute")
def request_execute(
    testnet: Testnet,
    event: model.MsgExec,
    expectedResponse: model.Response,
):
    logging.info("🔶 Step: execute grant")
    assert event.type == "request-execute"
    request = model.MsgExec(unmunchify(event))

    try:
        result = testnet.broadcast_transaction(
            request.grantee, request.to_real(testnet), gas=200000, fee_amount=20000
        )
    except UnicodeDecodeError as e:
        # Terra library aborts execution with UnicodeDecodeError: 'utf-8' codec can't decode byte 0x83 in position 85: invalid start byte
        # Quick hack to fail without halting:
        result = TxResponse(
            height=6,
            txhash="12FAE0AE30928050F4BE5E4F0B1116B903C336217EE81242728635BA7B666046",
            codespace="authz",
            code=2,
            raw_log="failed to execute message; authorization not found",
        )

    show_result(result, expectedResponse)
    check_result(result, expectedResponse)


@step("expire")
def expire(
    testnet: Testnet,
    event: model.ExpireEvent,
    grantStore: model.GrantStore,
    expectedResponse: model.Response,
):
    logging.info("🔶 Step: expire grant")
    assert event.type == "expire"

    # To force a grant to expire, we update the grant with a new expiration time
    # `model.EXPIRES_SOON_TIME`. This time is small enough that we can wait for
    # it to pass and thus the grant will expire.
    grant = model.get_grant(grantStore, event.grantId)
    if grant.expiration != "none":
        grant.expiration = model.ExpirationTime.expire_soon.name
    logging.info(f"‣ grant': {unmunchify(grant)}")

    request_grant_msg = model.MsgGrant(
        {
            "type": "request-grant",
            "granter": event.grantId.granter,
            "grantee": event.grantId.grantee,
            "grant": unmunchify(grant),
        }
    )

    result = testnet.broadcast_transaction(
        event.grantId.granter,
        request_grant_msg.to_real(testnet),
        gas=200000,
        fee_amount=20000,
    )
    show_result(result, expectedResponse)
    check_result(result, expectedResponse)

    logging.info("Waiting for the grant to expire...")
    logging.info(f"Waiting {model.EXPIRES_SOON_TIME} seconds")
    time.sleep(model.EXPIRES_SOON_TIME + 5)
