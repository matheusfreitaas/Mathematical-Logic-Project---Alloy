module PizzariaCampinaGrande
open util/ordering[Tempo]

-- Cria a noção temporal no projeto, utilizando a biblioteca util/ordering
sig Tempo {}

-- Cria uma assinatura da central de atendimento que possui várias pizzarias
one sig CentralDeAtendimento {
	pizzarias: set Pizzaria
}

-- Assinatura de uma pizzaria genérica, todas possuem um set de motoboy
abstract sig Pizzaria {
	motoboys: set Motoboy
}

-- Assinatura das pizzarias específicas
one sig FIlialNorte extends Pizzaria {}
one sig FIlialSul extends Pizzaria {}
one sig FIlialLeste extends Pizzaria {}
one sig FIlialOeste extends Pizzaria {}
one sig FIlialCentro extends Pizzaria {}

-- Assinatura de Motoboy que possui Cliente pra um dado Tempo e espera que também possui Cliente para um dado Tempo
sig Motoboy {
	cliente: Cliente -> Tempo,
	espera: Cliente -> Tempo
}

-- Assinatura de Cliente que pode possuir um conjunto de Pedido para um dado tempo
sig Cliente {
	pedidos: set Pedido -> Tempo
}

-- Assinatura dos pedidos
sig Pedido {}

-- Facts são condições que sempre devem acontecer durante a execução do programa
fact Pizzaria {
	-- O número de instancias de Pizzaria deve ser igual a 5, uma pra cada região
	#Pizzaria = 5

	-- Toda pizzaria deve estar ligada à central de atendimento
	all p: Pizzaria | one ca: CentralDeAtendimento | p in ca.pizzarias
}

fact Motoboy {
	-- O número de instancias de Motoboy deve ser igual a 15, 3 para cada pizzaria de cada região
	#Motoboy = 15

	-- Toda pizzaria deve ter o número de instancias de seus motoboys igual a 3
	all p: Pizzaria | #(p.motoboys) = 3

	-- Para cada duas pizzarias diferentes, se um motoboy é de uma pizzaria, então ele não é de outra / Um motoboy atende somente uma região
	all p1: Pizzaria, p2: Pizzaria - p1, m: Motoboy | m in p1.motoboys => m not in p2.motoboys

	-- Não existe um motoboy sem uma pizzaria / Todos os motoboys estão ligados à todas as pizzarias
	all m: Motoboy | one p: Pizzaria | m in p.motoboys

	-- Cada motoboy só pode estar atendendo a no máximo 1 único cliente num dado Tempo t
	all m: Motoboy, t: Tempo | #((m.cliente).t) <= 1

	-- Pra cada dois motoboys distintos, se um cliente está na lista de espera de um motoboy num dado Tempo t, então esse cliente não está na lista de espera de outor motoboy no mesmo Tempo t
	-- Resumindo: As listas de espera possuem clientes únicos / Um cliente nunca está na lista de espera de dois motoboys distintos
	all m1: Motoboy, m2: Motoboy - m1, c: Cliente, t: Tempo | c in (m1.espera).t => c not in (m2.espera).t
}

fact Cliente {
	-- Um cliente é atendido por um único motoboy / Um cliente nunca esta em 'cliente' de dois motoboys num mesmo Tempo t
	all c: Cliente, m1: Motoboy, m2: Motoboy - m1, t: Tempo | c in (m1.cliente).t => c not in (m2.cliente).t

	-- Se um cliente está sendo atendido por um motoboy, então o número de pedidos desse cliente num dado Tempo t é maior ou igual a 1
	-- Resumindo: Se um cliente está sendo atendido, então ele fez pelo menos um pedido
	all c: Cliente, m: Motoboy, t: Tempo | c in (m.cliente).t => #((c.pedidos).t) >= 1

	-- Em todo momento, todos os clientes devem ter feito pelo menos um pedido
	all c: Cliente, t: Tempo | #((c.pedidos).t) >= 1

	-- Se um cliente está sendo atendido num dado Tempo t, então ele não pode estar numa lista de espera de outro motoboy nesse mesmo tempo
	all c: Cliente, m1: Motoboy, m2: Motoboy - m1, t: Tempo | c in (m1.cliente).t => c not in (m2.espera).t

	-- Se um cliente está numa lista de espera de um motoboy num dado Tempo t, então outro cliente deve estar sendo atendido por esse motoboy
	all c1: Cliente, c2: Cliente - c1, m: Motoboy, t: Tempo | c1 in (m.espera).t => c2 in (m.cliente).t

	-- Se um cliente está sendo atendido por um motoboy num dado Tempo t, então ele não está na lista de espera daquele motoboy no mesmo Tempo t
	all c: Cliente, m: Motoboy, t: Tempo | c in (m.cliente).t => c not in (m.espera).t

	-- Se um cliente está na lista de espera de um motoboy pra um dado Tempo t, então ele deve ser cliente desse motoboy no próximo momento t'
	all c: Cliente, m: Motoboy, t: Tempo | let t' = t.next | c in (m.espera).t => c in (m.cliente).t' and c not in (m.espera).t'
}

fact Pedido {
	-- Todo pedido deve ter sido feito por um único cliente
	all p: Pedido, t: Tempo | one c: Cliente | p in (c.pedidos).t
}

-- O fact Traces explica como o programa deve funcionar
-- Provável de Massoni não perguntar sobre isso, mas está documentado
fact Traces {
	-- Traces chama init[first] onde first é uma instancia de Tempo, que representa o tempo inicial
	-- Abaixo do init temos tudo que pode acontecer com o programa, então: pra todo tempo exceto o último, existe algum cliente, motoboy e pedido tais que
	-- pode acontecer um addCliente[c, m, t, t'] (ou seja, um cliente pode ser adicionado), ou um delCliente[c, m , t, t'] (ou seja, algum cliente pode ser removido)
	-- pode acontecer um addPedido[p, c, t ,t'] (ou seja, um pedido pode ser feito), ou um delPedido[p, c, t, t'] (ou seja, algum pedido pode ser cancelado)
	init[first]
	all t: Tempo - last| let t' = t.next |
	some c: Cliente, m: Motoboy, p: Pedido |

	(addCliente[c, m, t, t'] or delCliente[c, m , t, t'] or addPedidoMotoboyEspecifico[p, c, m, t, t']) and
	(addPedido[p, c, t, t'] or delPedido[p, c, t, t'])
}

-- Preds são como funções que retornam verdadeiro ou falso
-- O pred init define o que deve acontecer no primeiro momento do programa
-- O corpo do init indica que não deve haver nenhum cliente vinculado a nenhum motoboy
pred init[t: Tempo] {
	no (Motoboy.cliente).t
}

/** Predicados são definidos da seguinte forma: deve-se especificar uma condição para o atual momento e uma outra condição
para o próximo momento, onde ambas devem ser satisfeitas, isso que irá dar a noção de temporalidade para o programa **/

-- O pred addCliente adiciona um cliente a um motoboy caso ele ja esteja atendendo alguém, caso contrário adiciona diretamente como cliente do motoboy
pred addCliente[c: Cliente, m: Motoboy, t, t': Tempo] {
	(#(m.cliente).t = 1) => ((m.espera).t = (m.espera).t + c) and
	((m.espera).t' = (m.espera).t - c) and
	((m.cliente).t' = c)

	(c not in getClientes[t]) => (getClientes[t'] = getClientes[t] + c) and
	(m.cliente).t' = (m.cliente).t + c
}

-- O pred delCliente remove um cliente de um motoboy e em seguida elimina todos os pedidos desse cliente
pred delCliente[c: Cliente, m: Motoboy, t, t': Tempo] {
	(c in getClientes[t]) => (getClientes[t'] = getClientes[t] - c) and
	(c in (m.cliente).t) => ((m.cliente).t' = (m.cliente).t - c) and

	all p: (c.pedidos).t | delPedido[p, c, t, t']
}

-- O pred addPedido adiciona um pedido a um cliente
pred addPedido[p: Pedido, c: Cliente, t, t': Tempo] {
	(p not in getPedidos[t]) => (getPedidos[t'] = getPedidos[t] + p) and
	(c.pedidos).t' = (c.pedidos).t + p
}

-- O pred delPedido remove/cancela um pedido de um cliente
pred delPedido[p: Pedido, c: Cliente, t, t': Tempo] {
	(p in getPedidos[t]) => (getPedidos[t'] = getPedidos[t] - p)
}

-- O pred addPedidoMotoboyEspecifico adiciona um pedido a um motoboy especifico
-- Deveria estar declarado no Traces, acabei esquecendo, ele pode perguntar sobre isso
pred addPedidoMotoboyEspecifico[p: Pedido, c: Cliente, m: Motoboy, t, t': Tempo] {
	addPedido[p, c, t, t'] and addCliente[c, m, t, t']
}

-- Fun são funções
-- Retorna todos os clientes que estão sendo atendidos em um dado Tempo t
fun getClientes[t: Tempo]: set Cliente {
	(Motoboy.cliente).t
}

-- Retorna todos os clientes de uma determinada região da cidade em um dado Tempo t
fun getClientesPizzaria[p: Pizzaria, t: Tempo]: set Cliente {
	((p.motoboys).cliente).t
}

-- Retorna todos os pedidos feitos por todos os clientes em um dado Tempo t
fun getPedidos[t: Tempo]: set Pedido {
	(Cliente.pedidos).t
}

-- Asserts verificam/testam que seu corpo sempre devem ser verdade, caso ocorra uma falha, o programa não é executado
-- Todo cliente deve possuir algum pedido em um determinado Tempo t
assert todosClientesPossuemPedidos {
	all  t: Tempo |  some getPedidos[t]
}

-- Todo motoboy deve atender no máximo um cliente
assert todosMotboysAtendeNoMaximoUmCliente {
	all m: Motoboy, t: Tempo | #((m.cliente).t) <= 1
}

-- Toda pizzaria é gerenciada por uma central de atendimento e possui 3 motoboys
assert todaPizzariaEstaEmUmCentralEPossui3Motoboys {
	all ca: CentralDeAtendimento, p:Pizzaria | p in ca.pizzarias and #(p.motoboys) = 3
}

-- Checks são utilizados apenas para os asserts, quando você deseja se um assert é válido, adicione um check <nomeDoAssert>
--check todaPizzariaEstaEmUmCentralEPossui3Motoboys for 15

--check todosMotboysAtendeNoMaximoUmCliente for 15

--check todosClientesPossuemPedidos for 15

run init for 15 but 10 Tempo, 5 Pedido
