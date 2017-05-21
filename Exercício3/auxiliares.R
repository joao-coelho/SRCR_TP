library(leaps)

# Saber quais os 4 atributos de entrada mais importantes para o cálculo no nível de fadiga
regg1 <- regsubsets(FatigueLevel ~ Performance.KDTMean + Performance.MAMean + Performance.MVMean +
					Performance.TBCMean + Performance.DDCMean + Performance.DMSMean + Performance.AEDMean +
					Performance.ADMSLMean, exaustao7N, nvmax = 4)

# Saber quais os 4 atributos de entrada mais importantes para o cálculo da Task em exercício
regg2 <- regsubsets(Performance.Task ~ Performance.KDTMean + Performance.MAMean + Performance.MVMean +
					Performance.TBCMean + Performance.DDCMean + Performance.DMSMean + Performance.AEDMean +
					Performance.ADMSLMean, exaustao7N, nvmax = 4)

# Saber quais os 4 atributos de entrada mais importantes para uma rede com ambos os neurónios de saída
regg3 <- regsubsets(FatigueLevel + Performance.Task ~ Performance.KDTMean + Performance.MAMean + Performance.MVMean +
					Performance.TBCMean + Performance.DDCMean + Performance.DMSMean + Performance.AEDMean +
					Performance.ADMSLMean, exaustao7N, nvmax = 4)
