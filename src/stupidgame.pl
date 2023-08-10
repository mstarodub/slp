play(State) :- stop(State,State).
play(State) :-
    pay_entrance(State,State1),
    dice_reward(State1,State2),
    play(State2).

stop([Player,Banker],_) :-
    Player1 is Player,
    Banker1 is Banker,
    write('Player = '), write(Player1),
    write('Banker = '), write(Banker1).
pay_entrance([Player,Banker],[Player-4,Banker+4]).
dice_reward([Player,Banker],[Player+D,Banker-D]) :- roll_dice(D).

1/6::roll_dice(1).
1/6::roll_dice(1).
1/6::roll_dice(2).
1/6::roll_dice(3).
1/6::roll_dice(4).
1/6::roll_dice(5).
1/6::roll_dice(6).
