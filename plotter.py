import matplotlib.pyplot as plt

# model 1
results_1 = [
    [(2, 0.89)],
    [(3, 0.1)],
    [(5, 3600)],
    [(3, 56.2)],
    [(5, 36.85)],
    [(2, 0.52)],
    [], # 7 time out
    [(12, 1542.19)],
    [(35, 3600)],
    [(15, 3600)],
    [], # 11 time out
    [(8, 3600)],
    [(6, 3600)],
    [(4, 3600)],
    [()], # 15 time out
    [(6, 3600)],
    [(10, 3600)],
    [()], # 18 time out

]

# model 2
results_2 = [
    [(2, 1.19)],
    [(2, 1.83), (3, 2.41)],
    [(5, 11.91)],
    [(3, 1.15)],
    [(5, 1.67)],
    [(2, 0.65), (2, 10.87)],
    [], # 7 time out
    [(11, 5.9), (12, 1967.88)],
    [(32, 24.4), (33, 34.14), (34, 41.52), (35, 62.14)],
    [(13, 608.19), (13, 3600)],
    [], # 11 time out
    [(7, 2180.74), (7, 3600)],
    [(6, 4,13)],
    [(4, 94.1)],
    [], # 15 time out
    [(6, 8.98), (8, 9.19), (9, 12.82)],
    [(7, 7.68), (11, 191.37)],
    [], # 18 time out
    [], # 19 time out
    [], # 20 time out
]

def plot_results(results, model_number):
    for instance in results:
        if len(instance) == 0:
            continue
        xs = [e[1] for e in instance]
        ys = [e[0] for e in instance]
        print(xs, ys)
        plt.scatter(xs, ys)
        plt.plot(xs, ys)

    plt.title(f'Maximizing the number of free weekends (model {model_number})')
    plt.ylabel('Number of free weekends')
    plt.xlabel('Runtime in seconds')
    plt.xscale('log')
    plt.show()

plot_results(results_2, 2)