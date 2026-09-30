import json
import sys
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

from expense import Expense, Status
from ledger import balances, settle_up
from split import split_equal


def split_body(body: dict) -> dict:
    amount = int(body["amount"])
    parts = int(body["parts"])
    if amount < 0 or parts < 1:
        raise ValueError("amount must be at least 0 and parts at least 1")
    return {"shares": split_equal(amount, parts)}


def balances_body(body: dict) -> dict:
    members = int(body["members"])
    if members < 1:
        raise ValueError("a group needs a member")
    expenses: list[Expense] = []
    for e in body["expenses"]:
        #@ invariant all(len(x.shares) == members for x in expenses)
        shares = [int(s) for s in e["shares"]]
        payer = int(e["payer"])
        if len(shares) != members or not 0 <= payer < members or any(s < 0 for s in shares):
            raise ValueError("an expense does not fit the group")
        expenses.append(Expense(payer, sum(shares), shares, Status(e["status"])))
    return {"balances": balances(members, expenses)}


def settle_body(body: dict) -> dict:
    owed = [int(b) for b in body["balances"]]
    if sum(owed) != 0:
        raise ValueError("balances must sum to zero")
    return {"transfers": [{"debtor": t.debtor, "creditor": t.creditor, "amount": t.amount} for t in settle_up(owed)]}


ROUTES = {"/api/split": split_body, "/api/balances": balances_body, "/api/settle": settle_body}


class Handler(BaseHTTPRequestHandler):
    def do_POST(self) -> None:
        route = ROUTES.get(self.path)
        if route is None:
            self.send_error(404)
            return
        body = json.loads(self.rfile.read(int(self.headers.get("Content-Length", "0"))))
        try:
            reply = route(body)
        except (KeyError, TypeError, ValueError) as err:
            self.send_response(400)
            reply = {"error": str(err)}
        else:
            self.send_response(200)
        data = json.dumps(reply).encode()
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)


if __name__ == "__main__":
    port = int(sys.argv[1]) if len(sys.argv) > 1 else 8787
    ThreadingHTTPServer(("127.0.0.1", port), Handler).serve_forever()
