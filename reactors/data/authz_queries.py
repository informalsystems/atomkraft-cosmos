import asyncio
import contextlib
import logging

from terra_proto.cosmos.authz.v1beta1 import QueryStub
from terra_proto.cosmos.bank.v1beta1 import QueryStub as QueryStubBank

from atomkraft.chain import Testnet


def query_grants(testnet: Testnet, granter, grantee):
    if logging.getLogger().isEnabledFor(logging.DEBUG):
        with contextlib.closing(testnet.get_grpc_channel()) as channel:
            stub = QueryStub(channel)
            result = asyncio.run(
                stub.grants(
                    granter=testnet.acc_addr(granter), grantee=testnet.acc_addr(grantee)
                )
            )
            logging.debug(f"grants from {granter} to {grantee}: {result.grants}")


def query_balance(testnet: Testnet, address):
    with contextlib.closing(testnet.get_grpc_channel()) as channel:
        stub = QueryStubBank(channel)
        result = asyncio.run(
            stub.balance(address=testnet.acc_addr(address), denom=testnet.denom)
        )
        return result.balance.amount


def query_all_balances(testnet: Testnet):
    if logging.getLogger().isEnabledFor(logging.DEBUG):
        balances = [f"{a}: {query_balance(testnet, a)}" for a in testnet.accounts.keys()]
        logging.debug(f"balances: {balances}")
