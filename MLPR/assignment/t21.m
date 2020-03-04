load('text_data.mat');
%a: augment the data
x_te = [x_test ones(length(x_test), 1)];
x_tr = [x_train ones(length(x_train), 1)];
%b
b_tr = rand(101, 1) * 10;
[X, fX, i] = minimize(b_tr, 't21b', 100, x_tr, y_train);

y_prob = 1./(1 + exp(-(x_te*X)));
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
y_prob_ml = 1./(1 + exp(-y_test.*(x_te*X)));
accuracy = tot / length(y_test);
y_mlog = mean(log(y_prob_ml));

y_prob_tr = 1./(1 + exp(-(x_tr*X)));
tot_t = 0;
for i = 1 : length(y_prob_tr)
    if (y_prob_tr(i) > 0.5) 
        temp = 1;
    else
        temp = -1;
    end
    if (temp == y_train(i))
        tot_t = tot_t + 1;
    end
end
y_prob_tr_ml = 1./(1 + exp(-y_train.*(x_tr*X)));
accuracy_t = tot_t / length(y_train);
y_mlog_t = mean(log(y_prob_tr_ml));
%standard error
std_err_a = sqrt(accuracy.*(1-accuracy)/size(y_prob, 1));
std_err_atr = sqrt(accuracy_t.*(1-accuracy_t)/size(y_prob_tr, 1));
std_err = sqrt(var(log(y_prob_ml))/size(y_prob, 1));
std_err_tr = sqrt(var(log(y_prob_tr_ml))/size(y_prob_tr, 1));