load('text_data.mat');
%a: augment the data
x_te = [x_test ones(length(x_test), 1)];
x_tr = [x_train ones(length(x_train), 1)];

[X, fX, i] = minimize([ones(101,1)',0]', @t23f, 10000, x_tr, y_train);

w = X(1: end -1);
eps = 1./(1+exp(-w(end)));
y_prob = 1./(1 + exp(-(x_te*w)));
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

y_prob_ml = 1./(1 + exp(-y_test.*(x_te*w)));
accuracy = tot / length(y_test);
y_mlog = mean(log(y_prob_ml));
