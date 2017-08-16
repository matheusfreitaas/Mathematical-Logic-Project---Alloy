module Taxi

--Assinatura da central.
sig Central{
	taxistas: set Taxista
}

--Assinatura do taxista.
sig Taxista{
	ligacao: lone Ligacao,
	corrida: lone Corrida,
	clientes: set Cliente
}

--Assinatura do cliente.
sig Cliente{}

--Assinatura do passageiro.
sig Passageiro{}

--Assinatura abstrata de ligação.
abstract sig Ligacao{}

--Assinatura dos diferentes tipos de ligações.
sig LigacaoCentral extends Ligacao{}

sig LigacaoCliente extends Ligacao{
	cliente: one Cliente
}

--Assinatura abstrata da corrida.
abstract sig Corrida{
	passageiros: set Passageiro
}

--Assinatura dos diferentes tipos de corrida.
sig CorridaDestinoUnico extends Corrida{}
sig CorridaMaisDeUmDestino extends Corrida{}

--Predicado que define que um taxista pode atender ligação se não estiver em outra.
pred atenderLigacao[t:Taxista]{
	no t.ligacao 
}

--Predicado que define que um taxista está disponível se não está em uma corrida.
pred taxistaDisponivel[t:Taxista]{
	no t.corrida
}

fact Corrida{
	--Toda corrida tem no pelo menos 1 passageiro.
	all c:Corrida | some c.passageiros
	
	--Toda corrida tem 1 taxista
	all c:Corrida | one c.~corrida

	--Toda corrida de mais de um detino deve ter no mínimo dois passageiros
	all c:CorridaMaisDeUmDestino | #c.passageiros > 1
	
	--Toda corrida só pode ter no máximo 4 passageiros.
	all c:Corrida | #c.passageiros <= 4
}	

fact Taxista{
	--Todo taxista tem uma central.
	all t:Taxista | one t.~taxistas

	--O taxista deve possuir o cliente para possuir uma ligação com o mesmo
	all t:Taxista | 
 	(t.ligacao in LigacaoCliente) =>
 	t.ligacao.cliente in t.clientes	
}

fact Passageiro{
	--Um passageiro só pode estar em uma corrida
	all p:Passageiro | one p.~passageiros
}

fact Cliente{
	--Todo cliente tem taxista.
	all c:Cliente | some c.~clientes

	--Um cliente não pode ter mais de uma ligação.
	all c:Cliente | one c.~cliente
}

fact Ligacao{
	--Uma ligação tem que ter um taxista.
	all l:Ligacao | one l.~ligacao
}

--Retorna todos os clientes de um dado taxista.
fun getClientes[t:Taxista]: set Cliente{
	t.clientes
}

--Retorna todos os taxistas de uma determinada central.
fun getTaxistas[c:Central]: set Taxista{
	c.taxistas
}

--Retorna todos os passageiros de uma determinada corrida.
fun getPassageiros[c:Corrida]: set Passageiro{
	c.passageiros
}

--Testes

-- Teste responsável por verificar que todo taxista tem exatamente 1 central
assert testeCentralTemTaxista{
	all t:Taxista |  #(t.~taxistas) =1
}

--Teste responsável por verificar se toda corrida tem um taxista
assert testeCorridaTemUmTaxista{
	all c:Corrida | #(c.~corrida) =1
}

--Teste responsável por verificar se toda corrida tem algum passageiro, e tenha no máximo 4
assert testeCorridaTemPassageiro{
	all c:Corrida | #(c.passageiros) >0 && #(c.passageiros) <=4

}

--Teste responsável por verificar se o taxista conhece o cliente da ligação de um cliente
assert testeTaxistaConheceClienteDaLigacao{
	all l:LigacaoCliente | #(l.cliente) =1 &&   (l.cliente) in (l.~ligacao).clientes
}

--Teste responsável por verificar se o taxista não tem corrida caso esteja disponível
assert testeTaxistaDisponivel{
	all t:Taxista | taxistaDisponivel[t] => no t.corrida
}


check testeCentralTemTaxista
check testeCorridaTemUmTaxista
check testeCorridaTemPassageiro
check testeTaxistaConheceClienteDaLigacao
check testeTaxistaDisponivel

pred show[]{}
run show for 3

