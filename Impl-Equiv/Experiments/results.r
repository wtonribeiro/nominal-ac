 # ============================================================================
 # Project     : Nominal A, AC and C Unification
 # File        : results.r
 # Authors     : Washington Lu\'is R. de Carvalho Segundo and
 #               Mauricio Ayala Rinc\'on 
 #               Universidade de Bras\'ilia (UnB) - Brazil
 #               Group of Theory of Computation
 #
 # Description : This file contains the data analysis of the results of the
 #               experiments
 #
 # Last Modified On: Sep 27, 2018.
 # ============================================================================


# Loads the libraries ggplot2 e dplyr

library(ggplot2)
library(dplyr)

# Loads the summary of the experiments in the variable "experiments"

experiments <- read.csv("results.csv")

# Variables "alpha", "alpha_A", "alpha_A_C", "alpha_A_C_AC" the sets of results 

alpha <- filter(experiments, set == "Alpha")
alpha_A <- filter(experiments, set == "Alpha and A")
alpha_A_C <- filter(experiments, set == "Alpha, A and C")
alpha_A_C_AC <- filter(experiments, set == "Alpha, A, C and AC")

# Defines the layout of the plots

point_style = geom_point(size = 1,  shape=21)
plot_theme = theme(plot.title = element_text(hjust = 0.5),
                   strip.text.x = element_text(size=13, margin = margin(.1, 0, .1, 0, "cm")),
                   strip.text.y = element_text(size=13), 
                   strip.background = element_rect(colour="white", fill="#FFFFFF"))
plot_wrap = facet_wrap(set ~ algorithm, scales = "free", nrow = 2)
plot_stat = stat_smooth(method = "auto", se = FALSE)
x_label = xlab ("Input size")
y_label = ylab("Time (secs.)")

# Defines the plots

alpha_plot = ggplot(alpha, aes(x = size, y = time)) + point_style +
             plot_theme + plot_wrap + plot_stat + x_label + y_label
alpha_A_plot = ggplot(alpha_A, aes(x = size, y = time)) + point_style +
  plot_theme + plot_wrap + plot_stat + x_label + y_label
alpha_A_C_plot = ggplot(alpha_A_C, aes(x = size, y = time)) + point_style +
  plot_theme + plot_wrap + plot_stat + x_label + y_label
alpha_A_C_AC_plot = ggplot(alpha_A_C_AC, aes(x = size, y = time)) + point_style +
  plot_theme + plot_wrap + plot_stat + x_label + y_label 

# Generates the plots

alpha_plot
alpha_A_plot
alpha_A_C_plot
alpha_A_C_AC_plot
