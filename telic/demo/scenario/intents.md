# Shop intents

Requirements that span the server and the checkout page. Intents local to one
file stay as comments in it.

## PRICE-AGREE
WHEN a customer checks out, the checkout page shall show exactly the amount the
server charges.
by: discounted_total, web/checkout.ts::displayTotal
