import choreography as chor

p1 = 'party1'
p2 = 'party2'

x = chor.constant(p1, 5)
xp = chor.send(p2, x)
y = chor.locally(p2, lambda x: x+1, xp)
yp = chor.send(p1, y)


