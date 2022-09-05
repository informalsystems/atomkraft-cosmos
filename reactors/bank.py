import asyncio
import logging
import time

from atomkraft.chain import Testnet
from modelator.pytest.decorators import step
from terra_sdk.core.bank import MsgSend
from terra_proto.cosmos.bank.v1beta1 import QueryStub

@step("Init")
def init(testnet: Testnet, action):
    logging.info("Step: Init")
    testnet.set_accounts(action.value.wallets)
    testnet.verbose = True
    testnet.oneshot()
    time.sleep(10)
    logging.info("Status: Testnet launched\n")


@step("Transfer")
def transfer(testnet: Testnet, action):
    logging.info("Step: Transfer")
    action = action.value

    sender_id = action.sender
    receiver_id = action.receiver
    amount = action.amount

    sender_addr = testnet.acc_addr(sender_id)
    receiver_addr = testnet.acc_addr(receiver_id)

    channel = testnet.get_grpc_channel()
    stub = QueryStub(channel)
    result = asyncio.run(
        stub.balance(
            address=sender_addr, denom=testnet.denom
        )
    )
    channel.close()
    logging.info(f"\tSender balance:    {result.balance.amount}")


    msg = MsgSend(sender_addr, receiver_addr, f"{amount}{testnet.denom}")

    result = testnet.broadcast_transaction(sender_id, msg, gas=200000, fee_amount=20000)

    logging.info(f"\tSender:    {sender_id} ({sender_addr})")
    logging.info(f"\tReceiver:  {receiver_id} ({receiver_addr})")
    logging.info(f"\tAmount:    {msg.amount}")

    if result.code == 0:
        logging.info("Status: Successful\n")
    else:
        logging.info("Status: Error")
        logging.info(f"\tcode: {result.code}")
        logging.info(f"\tlog:  {result.raw_log}\n")

    logging.debug(f"[MSG] {msg}")
    logging.debug(f"[RES] {result}")

    time.sleep(1)
