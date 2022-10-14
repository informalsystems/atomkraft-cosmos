import asyncio
from datetime import datetime
import contextlib
import logging

from terra_proto.cosmos.authz.v1beta1 import QueryStub
from terra_proto.cosmos.bank.v1beta1 import QueryStub as QueryStubBank

from atomkraft.chain import Testnet


def query_grants(testnet: Testnet, granter, grantee):
    logging.info(f"🔺 now: {datetime.now()}")
    with contextlib.closing(testnet.get_grpc_channel()) as channel:
        stub = QueryStub(channel)
        result = asyncio.run(
            stub.grants(
                granter=testnet.acc_addr(granter), grantee=testnet.acc_addr(grantee)
            )
        )
        logging.info(f"🔺 grants from {granter} to {grantee}: {result}")
        # logging.info(f"🔺 grant time: {datetime(result.grants[0].expiration)}")
        logging.info(f"🔺 now: {datetime.now()}\n")


def query_bank(testnet: Testnet, address):
    with contextlib.closing(testnet.get_grpc_channel()) as channel:
        stub = QueryStubBank(channel)
        result = asyncio.run(
            stub.balance(address=testnet.acc_addr(address), denom=testnet.denom)
        )
        logging.info(f"🔥 balance {address}: {result.balance.amount}")


def query_all_balances(testnet: Testnet):
    for acc in testnet.accounts.keys():
        query_bank(testnet, acc)
