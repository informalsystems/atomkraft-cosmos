import logging
from munch import unmunchify  # type: ignore
import re
import time
from timeit import default_timer as timer

from terra_proto.cosmos.base.abci.v1beta1 import TxResponse  # type: ignore

from atomkraft.chain import Testnet
from atomkraft.chain.utils import TmEventSubscribe
from modelator.pytest.decorators import step

logger = logging.getLogger("authz")

from reactors.data import authz_model as model
from reactors.data.authz_queries import query_all_balances, query_grants


def show_result(result: TxResponse, expected: model.Response):
    if result.code == 0:
        logger.info(f"Status:\tOK")
    else:
        logger.info(f"Status:\tERROR (code: {result.code}, log: {result.raw_log})")

    if expected.error == "none":
        assert expected.ok
        logger.info(f"Expected:\tOK\n")
    else:
        assert not expected.ok
        logger.info(f"Expected:\tERROR ({expected.error})\n")


def check_result(result: TxResponse, expected: model.Response):
    assert (result.code == 0) == (expected.error == "none")
    if result.code == 0:
        assert expected.error == "none"
    else:
        # the error message in the model may contain parentheses
        expected_error = expected.error.replace("(", "\\(").replace(")", "\\)")
        assert bool(re.search(expected_error, result.raw_log))


INITIAL_BALANCE = 1000000


@step("no-event")
def init(testnet: Testnet, Accounts: list[str], Validators: list[str]):
    logger.info("🔶 Step: init")

    testnet.set_accounts(sorted(Accounts))
    testnet.set_validators(sorted(Validators))
    testnet.set_account_balances(
        dict([(id, {"stake": INITIAL_BALANCE}) for id in sorted(Accounts)])
    )
    testnet.set_validator_balances(
        dict([(id, {"stake": INITIAL_BALANCE}) for id in sorted(Validators)])
    )
    testnet.verbose = True

    logger.info(f"Preparing testnet...")
    start_time = timer()
    testnet.prepare()
    logger.debug(f"Prapare time: {(timer() - start_time):.2f} seconds")

    logger.info(f"Spining up testnet...")
    start_time = timer()
    testnet.spinup()
    logger.debug(f"Spinup time: {(timer() - start_time):.2f} seconds")

    logger.info(f"Wait for testnet to be ready...")
    start_time = timer()
    with TmEventSubscribe({"tm.event": "NewBlock"}):
        logger.debug(f"Waiting time: {(timer() - start_time):.2f} seconds")
        logger.info("Testnet launched! 🚀\n")


@step("request-grant")
def request_grant(
    testnet: Testnet,
    event: model.MsgGrant,
    expectedResponse: model.Response,
):
    logger.info("🔶 Step: request grant")
    start_time = timer()

    request = model.MsgGrant(unmunchify(event))
    logger.info(f"request: {request}")

    result = testnet.broadcast_transaction(
        request.granter,
        request.to_real(testnet),
    )
    query_grants(testnet, request.granter, request.grantee)
    show_result(result, expectedResponse)
    check_result(result, expectedResponse)
    logger.debug(f"Elapsed time: {(timer() - start_time):.2f} seconds\n")


@step("request-revoke")
def request_revoke(
    testnet: Testnet,
    event: model.MsgRevoke,
    expectedResponse: model.Response,
):
    logger.info("🔶 Step: revoke grant")
    start_time = timer()

    request = model.MsgRevoke(unmunchify(event))
    logger.info(f"request: {request}")

    result = catch_unicode_decode_error(
        lambda: testnet.broadcast_transaction(
            request.granter,
            request.to_real(testnet),
        )
    )
    query_grants(testnet, request.granter, request.grantee)
    show_result(result, expectedResponse)
    check_result(result, expectedResponse)
    logger.debug(f"Elapsed time: {(timer() - start_time):.2f} seconds")


@step("request-execute")
def request_execute(
    testnet: Testnet,
    event: model.MsgExec,
    expectedResponse: model.Response,
):
    logger.info("🔶 Step: execute grant")
    start_time = timer()

    request = model.MsgExec(unmunchify(event))
    logger.info(f"request: {request}")

    result = catch_unicode_decode_error(
        lambda: testnet.broadcast_transaction(
            request.grantee,
            request.to_real(testnet),
        )
    )
    query_all_balances(testnet)
    show_result(result, expectedResponse)
    check_result(result, expectedResponse)
    logger.debug(f"Elapsed time: {(timer() - start_time):.2f} seconds")


@step("expire")
def expire(
    testnet: Testnet,
    event: model.ExpireEvent,
    expectedResponse: model.Response,
):
    logger.info("🔶 Step: expire grant")
    start_time = timer()

    # To force a grant to expire, we update the grant with a new expiration time
    # `model.EXPIRES_SOON_TIME`. This time is small enough that we can wait for
    # it to pass and thus the grant will expire. It cannot be a `past` time
    # because the request would be rejected.
    request = model.MsgGrant(
        {
            "type": "request-grant",
            "granter": event.grantId.granter,
            "grantee": event.grantId.grantee,
            "grant": {
                "authorization": unmunchify(event.authorization),
                "expiration": model.ExpirationTime.expire_soon.name,
            },
        }
    )
    result = testnet.broadcast_transaction(
        event.grantId.granter, request.to_real(testnet)
    )
    show_result(result, expectedResponse)
    check_result(result, expectedResponse)

    wait_time = model.EXPIRES_SOON_TIME + 1
    logger.info(f"Waiting {wait_time} seconds for the grant to expire...\n")
    time.sleep(wait_time)

    query_grants(testnet, event.grantId.granter, event.grantId.grantee)
    query_all_balances(testnet)
    logger.debug(f"Elapsed time: {(timer() - start_time):.2f} seconds")


# This is a quick hack to return an error message without halting the execution of the trace.
# There are two places where this happens:
# - https://github.com/cosmos/cosmos-sdk/blob/25e7f9bee2b35f0211b0e323dd062b55bef987b7/x/authz/keeper/keeper.go#L105
# - https://github.com/cosmos/cosmos-sdk/blob/25e7f9bee2b35f0211b0e323dd062b55bef987b7/x/authz/keeper/keeper.go#L212
# The protobuf library `betterproto`, used by terra.py, throws an exception `UnicodeDecodeError` when it is not able to
# decode to string a binary message that includes a wrong UTF-8 byte sequence.
# The error messages from the Authz module look like this:
#   b'failed to execute message; message index: 0: failed to update grant with key \x01\x14\x83\xc1\xde\xde\x080\xdctC\x8b...\nu4tD\x88\xb3\x14huI\x186\x15\x83\x86\xe8GA\xbeS\xa4j\xb4o\xf3M5/cosmos.bank.v1beta1.MsgSend: authorization not found'
def catch_unicode_decode_error(fn):
    try:
        return fn()
    except UnicodeDecodeError:
        return TxResponse(
            codespace="authz",
            code=2,
            raw_log="failed to execute message (UnicodeDecodeError)",
        )
