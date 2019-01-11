library(ggplot2)
library(dplyr)

setwd("/home/wlr/nominal-ac/Impl-Equiv/Experiments") 


# Loads the summary of the experiments in the variable "experiments"

experiments <- read.csv("results.csv")

alpha_generated <- filter(experiments, set == "Alpha", algorithm == "Generated")
alpha_improved <- filter(experiments, set == "Alpha", algorithm == "Improved")

alpha_A_generated <- filter(experiments, set == "Alpha and A", algorithm == "Generated")
alpha_A_improved <- filter(experiments, set == "Alpha and A", algorithm == "Improved")

alpha_A_C_generated <- filter(experiments, set == "Alpha, A and C", algorithm == "Generated")
alpha_A_C_improved <- filter(experiments, set == "Alpha, A and C", algorithm == "Improved")

alpha_A_C_AC_generated <- filter(experiments, set == "Alpha, A, C and AC", algorithm == "Generated")
alpha_A_C_AC_improved <- filter(experiments, set == "Alpha, A, C and AC", algorithm == "Improved")

###########

ggplot(alpha_generated, aes(x = size, y = time)) + geom_point(size = 1,  shape=21) + 
  xlab("Input size") + ylab("Time (secs.)") + stat_smooth(method = "auto", se = FALSE)

ggplot(alpha_improved, aes(x = size, y = time)) + geom_point(size = 1,  shape=21) + 
  xlab("Input size") + ylab("Time (secs.)") + stat_smooth(method = "auto", se = FALSE)

###########

ggplot(alpha_A_generated, aes(x = size, y = time)) + geom_point(size = 1,  shape=21) + 
  xlab("Input size") + ylab("Time (secs.)") + stat_smooth(method = "auto", se = FALSE)

ggplot(alpha_A_improved, aes(x = size, y = time)) + geom_point(size = 1,  shape=21) + 
  xlab("Input size") + ylab("Time (secs.)") + stat_smooth(method = "auto", se = FALSE)


###########

ggplot(alpha_A_C_generated, aes(x = size, y = time)) + geom_point(size = 1,  shape=21) + 
  xlab("Input size") + ylab("Time (secs.)") + stat_smooth(method = "auto", se = FALSE)

ggplot(alpha_A_C_improved, aes(x = size, y = time)) + geom_point(size = 1,  shape=21) + 
  xlab("Input size") + ylab("Time (secs.)") + stat_smooth(method = "auto", se = FALSE)


###########

ggplot(alpha_A_C_AC_generated, aes(x = size, y = time)) + geom_point(size = 1,  shape=21) + 
  xlab("Input size") + ylab("Time (secs.)") + stat_smooth(method = "auto", se = FALSE)

ggplot(alpha_A_C_AC_improved, aes(x = size, y = time)) + geom_point(size = 1,  shape=21) + 
  xlab("Input size") + ylab("Time (secs.)") + stat_smooth(method = "auto", se = FALSE)




