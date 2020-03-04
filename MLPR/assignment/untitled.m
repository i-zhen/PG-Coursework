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
%y_prob_ml = 1./(1 + exp(-y_prob.*(x_te*samples())));
accuracy = tot / length(y_prob);
%y_mlog = mean(log(y_prob_ml));