
library("neuralnet")
library("hydroGOF")
library("readr")

# ---- Ler ficheiro com dados para treinar rede ----

# dataset para identificar os 7 níveis de exaustão
# NOTA: "path" representa o caminho no computador pessoal até ao ficheiro a ler
exaustao <- read.csv("path\\exaustao.csv", header = TRUE, sep = ",", dec = ".", stringsAsFactors = FALSE)
exaustao7N <- exaustao[sample(nrow(exaustao)), ]

# Converter Performance.Task em valores numéricos
# Work = 1
# office = 2
# programming = 3
exaustao7N$Performance.Task[exaustao7N$Performance.Task == "Work"] <- 1
exaustao7N$Performance.Task[exaustao7N$Performance.Task == "office"] <- 2
exaustao7N$Performance.Task[exaustao7N$Performance.Task == "programming"] <- 3
exaustao7N$Performance.Task <- parse_integer(exaustao7N$Performance.Task)



# Função que retorna o subset de teste dependendo da fórmula escolhida
getSubset <- function(aux, testset) {

	if (aux[2] == "FatigueLevel") {
		teste01 <- subset(testset, select = c("Performance.DDCMean", "Performance.MAMean", "Performance.MVMean", "Performance.KDTMean"))
	}
	else {
		if (aux[2] == "Performance.Task") {
			teste01 <- subset(testset, select = c("Performance.KDTMean", "Performance.DMSMean", "Performance.DDCMean", "Performance.AEDMean"))
		}
		else {
			teste01 <- subset(testset, select = c("Performance.MAMean", "Performance.MVMean", "Performance.DDCMean", "Performance.ADMSLMean"))
		}
	}
	return (teste01)
}


# Função que retorna uma neuralnet
neuralTrain <- function(trainset, hidden, testset, algorithm = "rprop+", threshold = 0.1,
                        formula = Performance.Task + FatigueLevel ~ Performance.MAMean + Performance.MVMean +
																	Performance.DDCMean + Performance.ADMSLMean) {

	if (algorithm == "backprop") {
		nNet <- neuralnet(formula, trainset, algorithm = algorithm, learningrate = 0.1, hidden = hidden, threshold = threshold, lifesign = "full", linear.output = FALSE)
	}
	else {
		nNet <- neuralnet(formula, trainset, algorithm = algorithm, hidden = hidden, threshold = threshold, lifesign = "full")
	}

	aux <- strsplit(as.character(formula), "~")

	teste <- getSubset(aux, testset)
  
  	nNet$results <- compute(nNet, teste)

  	if (aux[2] == "FatigueLevel + Performance.Task" || aux[2] == "Performance.Task + FatigueLevel") {
  		resultsT <- data.frame(actual = testset$Performance.Task, prediction = nNet$results$net.result)
  		resultsF <- data.frame(actual = testset$FatigueLevel, prediction = nNet$results$net.result)
  		nNet$prediction1 <- round(resultsT$prediction.1)
  		nNet$prediction2 <- round(resultsT$prediction.2)
  		print("FatigueLevel:")
  		nNet$rmse1 <- rmse(c(resultsF$actual), c(nNet$prediction1))
  		print(nNet$rmse1)
  		print("Performance.Task:")
  		nNet$rmse2 <- rmse(c(resultsT$actual), c(nNet$prediction2))
  		print(nNet$rmse2)
  	}
  	else {
  		if (aux[2] == "FatigueLevel") {
  			results <- data.frame(actual = testset$FatigueLevel, prediction = nNet$results$net.result)
  			nNet$prediction <- round(results$prediction)
  			print("FatigueLevel:")
  			nNet$rmse <- rmse(c(results$actual), c(nNet$prediction))
  			print(nNet$rmse)
  		}
  		else {
  			results <- data.frame(actual = testset$Performance.Task, prediction = nNet$results$net.result)
  			nNet$prediction <- round(results$prediction)
  			print("Performance.Task:")
  			nNet$rmse <- rmse(c(results$actual), c(nNet$prediction))
  			print(nNet$rmse)
  		}
  	}
  
  	return (nNet)
}



# vários trainsets para o dataset exaustao7N
trainset1a <- exaustao7N[1:100, ]
trainset1b <- exaustao7N[1:200, ]
trainset1c <- exaustao7N[1:400, ]
trainset1d <- exaustao7N[1:600, ]

# vários testsets para o dataset exaustao7N
testset1a <- exaustao7N[601:nrow(exaustao7N), ]
testset1b <- exaustao7N[601:751, ]
testset1c <- exaustao7N[601:651, ]


# Conversão do dataset de input para 2 níveis de exaustão (ter ou não ter)
binFat <- function(dataset) {
	
	exaustaoBin <- dataset
	exaustaoBin$FatigueLevel[exaustaoBin$FatigueLevel <= 3] <- 0
	exaustaoBin$FatigueLevel[exaustaoBin$FatigueLevel > 3] <- 1
  
	return (exaustaoBin)
}

# Criação de um dataset com o nível de fadiga binário
exaustaoBin <- binFat(exaustao7N)

# vários trainsets para o dataset2
trainset2a <- exaustaoBin[1:100, ]
trainset2b <- exaustaoBin[1:200, ]
trainset2c <- exaustaoBin[1:400, ]
trainset2d <- exaustaoBin[1:600, ]

# vários testsets para o dataset2
testset2a <- exaustaoBin[601:nrow(exaustaoBin), ]
testset2b <- exaustaoBin[601:751, ]
testset2c <- exaustaoBin[601:651, ]


# Conversão do dataset para o melhor agrupamento de níveis de fadiga
bestFat <- function(dataset) {

	exaustaoBest <- dataset
	exaustaoBest$FatigueLevel[exaustaoBest$FatigueLevel < 3] <- 1
	exaustaoBest$FatigueLevel[exaustaoBest$FatigueLevel == 3] <- 2
  	exaustaoBest$FatigueLevel[exaustaoBest$FatigueLevel == 4] <- 3
  	exaustaoBest$FatigueLevel[exaustaoBest$FatigueLevel > 4] <- 4
  
  return(exaustaoBest);
}

# Criação de um dataset com o nível de fadiga na melhor escala
exaustaoBest <- bestFat(exaustao7N)

# vários trainsets para o dataset3
trainset3a <- exaustaoBest[1:100, ]
trainset3b <- exaustaoBest[1:200, ]
trainset3c <- exaustaoBest[1:400, ]
trainset3d <- exaustaoBest[1:600, ]

# vários testsets para o dataset3
testset3a <- exaustaoBest[601:nrow(exaustaoBest), ]
testset3b <- exaustaoBest[601:751, ]
testset3c <- exaustaoBest[601:651, ]



# Fórmula para representar uma rede com 2 neurónios de Output
# formula Fadiga + Task
formulaFatTask <- FatigueLevel + Performance.Task ~ Performance.MAMean + Performance.MVMean +
													Performance.DDCMean + Performance.ADMSLMean



# Fórmulas para representar Fadiga e Task em redes separadas, cada uma com o neurónio de Output correspondente:

# formula Fadiga
formulaFatigue <- FatigueLevel ~ Performance.DDCMean + Performance.MAMean +
								 Performance.MVMean + Performance.KDTMean

# formula Task
formulaTask <- Performance.Task ~ Performance.KDTMean + Performance.DMSMean +
								  Performance.DDCMean + Performance.AEDMean




# Testar a função de treino de rede

# Rede com 7 níveis de fadiga
neuralNormal <- neuralTrain(trainset = trainset1a, hidden = c(6,6), testset = testset1a, formula = formulaFatTask)

neuralNormal2 <- neuralTrain(trainset = trainset1b, hidden = c(8,10), testset = testset1a, algorithm = "backprop", formula = formulaFatigue)

neuralNormal3 <- neuralTrain(trainset = trainset1a, hidden = c(6), testset = testset1b, formula = formulaTask)

# Rede com 2 níveis de fadiga
neuralBin1 <- neuralTrain(trainset = trainset2a, hidden = c(4,10,5), testset = testset2c, formula = formulaTask, threshold = 0.05)

neuralBin2 <- neuralTrain(trainset = trainset2b, hidden = c(6,5), testset = testset2a, formula = formulaFatigue, algorithm = "rprop-")

# Rede com 4 níveis de fadiga
neuralBest1 <- neuralTrain(trainset = trainset3a, hidden = c(10), testset = testset3c, formula = formulaFatigue)

neuralBest2 <- neuralTrain(trainset = trainset3c, hidden = c(8), testset = testset3a, algorithm = "slr")
