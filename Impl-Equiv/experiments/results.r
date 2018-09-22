library(ggplot2)
library(dplyr)


experiments <- read.csv("results.csv")

alpha <- filter(experiments, set == "Alpha")
alpha_A <- filter(experiments, set == "Alpha and A")
alpha_A_C <- filter(experiments, set == "Alpha, A and C")
alpha_A_C_AC <- filter(experiments, set == "Alpha, A, C and AC")

point_style = geom_point(size = 1,  shape=21)
plot_theme = theme(strip.text.x = element_text(size=10, margin = margin(.1, 0, .1, 0, "cm")),
                   strip.text.y = element_text(size=10), 
                   strip.background = element_rect(colour="white", fill="#FFFFFF"))
plot_wrap = facet_wrap(set ~ algorithm, scales = "free", nrow = 6)
plot_stat = stat_smooth(method = "auto", se = FALSE)
x_label = xlab ("Input size")
y_label = ylab("Time (secs.)")


alpha_plot = ggplot(alpha, aes(x = size, y = time)) + point_style +
             plot_theme + plot_wrap + plot_stat + x_label + y_label
alpha_A_plot = ggplot(alpha_A, aes(x = size, y = time)) + point_style +
  plot_theme + plot_wrap + plot_stat + x_label + y_label
alpha_A_C_plot = ggplot(alpha_A_C, aes(x = size, y = time)) + point_style +
  plot_theme + plot_wrap + plot_stat + x_label + y_label
alpha_A_C_AC_plot = ggplot(alpha_A_C_AC, aes(x = size, y = time)) + point_style +
  plot_theme + plot_wrap + plot_stat + x_label + y_label

alpha_plot
alpha_A_plot
alpha_A_C_plot
alpha_A_C_AC_plot


