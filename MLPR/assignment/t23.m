load('text_data.mat');
%a: augment the data
x_te = [x_test ones(length(x_test), 1)];
x_tr = [x_train ones(length(x_train), 1)];

samples = slice_sample(1000, 0, @t23f, [ones(101,1)', 0.5, log(1)]', 0.2, true, x_tr, y_train);

xlabel('epsilon');
ylabel('log(lambda)');
hold on;
scatter(samples(end-1,:), samples(end,:));

for i = 1 : 1000
    y_pred = y_pred + x_te * samples(1:end-2,i);
end

y_prob = mean(y_pred, 2);

tot = 0;
for i = 1 : length(y_prob)
    if (y_prob(i) > 0.5) 
        temp = 1;
    else
        temp = -1;
    end
    if (temp == y_test(i))
        tot = tot + 1;
    end
end

accuracy = tot / length(y_prob);