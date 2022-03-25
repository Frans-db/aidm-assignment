import matplotlib.pyplot as plt

# model 2
results_2 = [
    [(2, 1.19)],
    [(2, 1.83), (3, 2.41)],
    [(5, 11.91)],
    [(3, 1.15)],
    [(5, 1.67)],
    [(2, 0.65), (2, 10.87)],
    [], # 7 time out
    [(11, 5.9)],
    [(12, 1967.88)],
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