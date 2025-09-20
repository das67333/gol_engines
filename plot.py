import pandas as pd
import matplotlib.pyplot as plt

# Загружаем данные
df = pd.read_csv("iteration_times.csv", header=None, names=["time_ns"])

# Гистограмма
plt.hist(df["time_ns"], bins=50, range=(0, 1000))
plt.xlabel("Iteration time (ns)")
plt.ylabel("Relative frequency")
plt.title("Distribution of iteration times")
# plt.show()
plt.savefig("hist.png", dpi=200)
