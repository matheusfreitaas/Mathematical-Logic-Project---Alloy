module Taxi

sig Taxista{
	ligacao: lone Ligacao,
	corrida: lone Corrida,
	clientes: set Cliente,
	passageiros: set Passageiro
}

abstract sig Ligacao{}

sig LigacaoCentral extends Ligacao{}

sig LigacaoCliente extends Ligacao{
	cliente: one Cliente
}

sig Corrida{}

sig Cliente{}

sig Passageiro{}

pred atenderLigacao[t:Taxista]{
	no t.ligacao 
}

pred taxistaDisponivel[t:Taxista]{
	no t.passageiros 
}

fact ligacaoTemTaxista{
	all l:Ligacao | one l.~ligacao
}

fact ligacaoClienteValida{
	all t:Taxista | 
	(t.ligacao in LigacaoCliente) =>
	t.ligacao.cliente in t.clientes
}

fact clienteTemTaxista{
	all c:Cliente | some c.~clientes
}

fact corridaTemTaxista{
	all c:Corrida | one c.~corrida
}

fact umTaxistaPorPassageiro{
	all p:Passageiro | one p.~passageiros
}

fact corridaComNoMinimoUmPassageiro{
	all t:Taxista | 
	one t.corrida <=>
	some t.passageiros 
}

fact limiteDePassageiros{
	all t:Taxista | #t.passageiros < 6
}

pred show[]{}
run show for 5
