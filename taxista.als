module Taxi

--Assinatura da central.
sig Central{
	taxistas: set Taxista,
	ligacoes: set LigacaoCentral
}

--Assinatura do taxista.
sig Taxista{
	ligacao: lone LigacaoCliente,
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
sig LigacaoCentral extends Ligacao{
	passageiro: one Passageiro
}
sig LigacaoCliente extends Ligacao{
	cliente: one Cliente
}

--Assinatura abstrata da corrida.
abstract sig Corrida{
	passageiros: set Passageiro
}

--Assinatura dos diferentes tipos de corrida.
sig CorridaMesmoLugar extends Corrida{}
sig CorridaLugarDiferente extends Corrida{}

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
	
	--Toda corrida só pode ter no máximo 4 passageiros.
	all c:Corrida | #c.passageiros <= 4
}	

fact Taxista{
	--Todo taxista tem uma central.
	all t:Taxista | one t.~taxistas
}

fact Passageiro{
	--Um passageiro só pode estar em uma ligação.
	all p:Passageiro | one p.~passageiro

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
	all l:LigacaoCliente | one l.~ligacao

	--Uma ligação tem que ter uma central.
	all l:LigacaoCentral | one l.~ligacoes
	
}

--Retorna todos os clientes de um dado taxista.
fun getClientes[t:Taxista]: set Cliente{
	t.clientes
}

--Retorna todos os taxistas de uma determinada central.
fun getTaxistas[c:Central]: set Taxista{
	c.taxistas
}

--Retorna todas as chamadas de uma determinada central.
fun getLigacoes[c:Central]: set Ligacao{
	c.ligacoes
}

--Retorna todos os passageiros de uma determinada corrida.
fun getPassageiros[c:Corrida]: set Passageiro{
	c.passageiros
}

--Testes


pred show[]{}
run show for 5

