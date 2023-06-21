module Checker#(
   parameter   NUM_OF_STATES='d11,                             NUM_OF_STATES_WIDTH=$clog2(NUM_OF_STATES),
                NUM_SUPPORTED_LANGUAGES='d4 ,                   NUM_SUPPORTED_LANGUAGES_WIDTH=$clog2(NUM_SUPPORTED_LANGUAGES),
                NUM_OF_TRIES='d5 ,                              NUM_OF_TRIES_WIDTH=$clog2(NUM_OF_TRIES),
                NUM_OF_OPERATION='d4 ,                          NUM_OF_OPERATION_WIDTH=$clog2(NUM_OF_OPERATION),
                SAVED_ACCOUNTS='d10 ,                           ACCOUNT_NUMBER_WIDTH=$clog2(SAVED_ACCOUNTS),
                PASSWORD_WIDTH='d16 ,                           BALANCE_WIDTH='d16
                   

)(
        input wire clk,
        input wire rst,
        input wire CardInserted,
        input wire [BALANCE_WIDTH-1:0] Cash_Amount,
        input wire [ACCOUNT_NUMBER_WIDTH-1:0] Acc_Number,

        input wire [NUM_OF_STATES_WIDTH-1:0] ControlUnit_CurrentState,
        input wire ControlUnit_OutWritePasswordEn,
        input wire [PASSWORD_WIDTH-1:0] ControlUnit_InKeypadPassword,
        input wire [PASSWORD_WIDTH-1:0] ControlUnit_InAccountPassword,

        input wire [PASSWORD_WIDTH+BALANCE_WIDTH:0] RAM_Accounts  [0:SAVED_ACCOUNTS-1] ,
        input wire [ACCOUNT_NUMBER_WIDTH-1:0] RAM_InAddress,
        input wire [BALANCE_WIDTH-1:0] RAM_OutReadBalance
        


);


property insert_card;
        @(posedge clk) disable iff (~rst)
        $rose(CardInserted)|=> (ControlUnit_CurrentState=='d1);
endproperty


property new_password;
        @(posedge clk) disable iff (~rst)
        $rose(ControlUnit_OutWritePasswordEn) |=> (RAM_Accounts[Acc_Number][PASSWORD_WIDTH+BALANCE_WIDTH-1:PASSWORD_WIDTH+BALANCE_WIDTH-16]!= 
        $past(RAM_Accounts[Acc_Number][PASSWORD_WIDTH+BALANCE_WIDTH-1:PASSWORD_WIDTH+BALANCE_WIDTH-16]));
endproperty

property deactivating_account;
  @(posedge clk) disable iff (~rst)
    ((ControlUnit_CurrentState == 'b0010) && (ControlUnit_InKeypadPassword != ControlUnit_InAccountPassword)) [*NUM_OF_TRIES] |=> ##[1:3] 
    (RAM_Accounts[Acc_Number][0] != $past(RAM_Accounts[Acc_Number][0])) ;
endproperty

property balance_update;
  @(posedge clk) disable iff(!rst)
   (ControlUnit_CurrentState == 'b0111) || (ControlUnit_CurrentState == 'b0101) |=>
    $changed((RAM_Accounts[RAM_InAddress]));
endproperty


property with_draw_more_than_balance;
  @(posedge clk) disable iff(!rst)
   (ControlUnit_CurrentState == 'b0101) |-> (Cash_Amount <= RAM_OutReadBalance);
endproperty

CARD_INSERT_ASSERT : assert property (insert_card);
NEW_PASSWORD_ASSERT :assert property (new_password);
DEACTIVATE_ASSERT : assert property (deactivating_account);
BALANCE_UPDATE_ASSERT : assert property (balance_update);
WITH_DRAW_ERROR_ASSERT : assert property (with_draw_more_than_balance);

endmodule