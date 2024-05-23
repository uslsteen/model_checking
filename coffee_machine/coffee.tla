--------------------------------- MODULE coffee ---------------------------------
EXTENDS Integers, TLC, Sequences


(*********************************** VARIABLES ***********************************)
(*--algorithm CoffeeMachine
variables
    start = FALSE, 
    heated = FALSE, 
    water = FALSE, 
    milk = FALSE,
    waited_time = 0, 
    water_level = 10, 
    grounds_level = 0, 
    milk_level = 10;

procedure GetMilkCoffee() 
begin
    s6:
        if (water_level > 0 /\ milk_level > 0) then
            water_level := water_level - 1;
            milk_level := milk_level - 1;
            water := FALSE;
            grounds_level :=  grounds_level + 2;
            waited_time := 0;
    s7:
        waited_time := waited_time + 5;
        milk := FALSE;
    end if;
end procedure;

procedure GetBlackCoffee() 
begin
    s5:
        if (water_level > 1) then
            water_level := water_level - 2;
            water := FALSE;
            grounds_level :=  grounds_level + 2;
            waited_time := 0
    end if;
end procedure;

procedure RunCoffee() 
begin
    begin_process:
    \*
        await water = (water_level = 0);
        await milk = (milk_level = 0);

        if (water) then
            s3:
                if (grounds_level > 0) then
                    waited_time := waited_time + 5;
                    grounds_level := 0;
                end if;

            s4:
                if (milk = FALSE) then
                    call GetBlackCoffee();
                else
                    call GetMilkCoffee();
                end if;
        end if;
    \*
    check_timer:
        if (waited_time > 30) then
            heated := FALSE;
            goto end_process;
        else
            goto begin_process;
        end if;

    end_process: return;
end procedure;

fair process Main = "Main"
begin
    s1:
        start := TRUE;

    s2:
        if (water_level > 0) then
            heated := TRUE;
            water_level := water_level - 1;

            call RunCoffee();
        else
            goto s0;
        end if;
    s0:
        start := FALSE;
end process;

fair process User = "User" begin
    init:
        start := TRUE;
        heated := TRUE;
end process;

end algorithm;*)
====