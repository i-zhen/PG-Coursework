load('text_data.mat');

x_te = [x_test ones(length(x_test), 1)];
x_tr = [x_train ones(length(x_train), 1)];

b_tr = ones(101, 1) ;
[X, fX, i] = minimize(b_tr, 't21b', 10000, x_tr(1:100,:), y_train(1:100,:));

y_prob_tr = 1./(1 + exp(-(x_te*X)));
tot_t = 0;
for i = 1 : size(y_prob_tr, 1)
    if (y_prob_tr(i) > 0.5) 
        temp = 1;
    else
        temp = -1;
    end
    if (temp == y_test(i))
        tot_t = tot_t + 1;
    end
end
accuracy = tot_t / size(y_test, 1);
y_mlog_t = mean(log(y_prob_tr));