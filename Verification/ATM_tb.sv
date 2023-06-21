`timescale 1ns/1ps

module ATM_tb #(
    parameter   NUM_OF_STATES='d11,                             NUM_OF_STATES_WIDTH=$clog2(NUM_OF_STATES),
                NUM_SUPPORTED_LANGUAGES='d4 ,                   NUM_SUPPORTED_LANGUAGES_WIDTH=$clog2(NUM_SUPPORTED_LANGUAGES),
                NUM_OF_TRIES='d5 ,                              NUM_OF_TRIES_WIDTH=$clog2(NUM_OF_TRIES),
                NUM_OF_OPERATION='d4 ,                          NUM_OF_OPERATION_WIDTH=$clog2(NUM_OF_OPERATION),
                SAVED_ACCOUNTS='d10 ,                           ACCOUNT_NUMBER_WIDTH=$clog2(SAVED_ACCOUNTS),
                PASSWORD_WIDTH='d16 ,                           BALANCE_WIDTH='d16
);

  // Inputs
  reg                                                 clk;
  reg                                                 rst;
  reg                                                 Card_Inserted;
  reg [ACCOUNT_NUMBER_WIDTH-1:0]                      Acc_Number;
  reg [NUM_SUPPORTED_LANGUAGES_WIDTH-1:0]             Language;
  reg [PASSWORD_WIDTH-1:0]                            Password;
  reg [NUM_OF_OPERATION_WIDTH-1:0]                    Operation;
  reg                                                 Another_Operation_Button;
  reg [BALANCE_WIDTH-1:0]                             Cash_Amount ;
  reg                                                 Money_Counter_Valid;
  reg [BALANCE_WIDTH-1:0]                             Money_Counter_Amount;
  wire                                                Money_Drawer_En;



  // Outputs

  // Instantiate the DUT
  ATM #(
                .NUM_OF_STATES(NUM_OF_STATES),                             .NUM_OF_STATES_WIDTH(NUM_OF_STATES_WIDTH),
                .NUM_SUPPORTED_LANGUAGES(NUM_SUPPORTED_LANGUAGES),         .NUM_SUPPORTED_LANGUAGES_WIDTH(NUM_SUPPORTED_LANGUAGES_WIDTH),
                .NUM_OF_TRIES(NUM_OF_TRIES),                               .NUM_OF_TRIES_WIDTH(NUM_OF_TRIES_WIDTH),
                .NUM_OF_OPERATION(NUM_OF_OPERATION),                       .NUM_OF_OPERATION_WIDTH(NUM_OF_OPERATION_WIDTH),
                .SAVED_ACCOUNTS(SAVED_ACCOUNTS) ,                          .ACCOUNT_NUMBER_WIDTH(ACCOUNT_NUMBER_WIDTH),
                .PASSWORD_WIDTH(PASSWORD_WIDTH) ,                          .BALANCE_WIDTH(BALANCE_WIDTH)
)DUT (
    .clk(clk),
    .RST(rst),
    .Card_Valid(Card_Inserted),
    .Card_Number(Acc_Number),
    .Language(Language),
    .KeyPad_Balance(Cash_Amount), //used in withdrawing the money
    .KeyPad_Password(Password),
    .Operation_Selection(Operation),
    .Money_Counter_Valid(Money_Counter_Valid),
    .Money_Counter_Amount(Money_Counter_Amount), //used in depositing money in account
    .In_Another_Operation_Wanted(Another_Operation_Button),
    .Money_Drawer_En(Money_Drawer_En)
  );


  //----------------reading the values from the golden reference--------//
  /*reg [PASSWORD_WIDTH-1:0]  password_MEM  [ACCOUNT_NUMBER_WIDTH-1:0];
  reg [BALANCE_WIDTH-1:0]   balance_MEM   [ACCOUNT_NUMBER_WIDTH-1:0];
  reg                       active_status [ACCOUNT_NUMBER_WIDTH-1:0];   
  initial begin
    $readmemb("Passwords.txt",password_MEM);
    $readmemb("Balances.txt",balance_MEM);
    $readmemb("Active.txt",active_status);

  end*/

  // Initialize inputs
  initial begin
    clk = 0;
    rst = 0;
    Card_Inserted = 0;
    Acc_Number = 0;
    Language = 0;
    Cash_Amount = 0;
    Password = 0;
    Operation = 0;
    Money_Counter_Valid = 0;
    Money_Counter_Amount = 0;
    Another_Operation_Button = 0;
  
    #10 rst = 1;

    //client 3 : password right -> with draw operation = 90 -> balance = 1841 -> 1751
    #10 Card_Inserted = 1;
    #10 Acc_Number = 2;  Card_Inserted = 0;
    #10 Language = 1;
    #10 Password = 'b0001_0010_1011_0110;
    #10 Operation = 'b0;
    #10 Cash_Amount = 90;
    #30;
  //client 4 : password wrong -> password right -> depoist = 800 -> balance = 7343 -> 8143
    #10 Card_Inserted = 1;
    #10 Acc_Number = 3; Card_Inserted = 0;
    #10 Language = 1;
    #10 Password = 'b1;
    #10 Password = 'b0010_0001_0111_1110;
    #10 Operation = 1;
    #10 Money_Counter_Amount = 800;
        Money_Counter_Valid = 1'b1;
    #30;

    //client 5 : password wrong -> password wrong - > password right -> show balance operation -> balance = 2653
    #10 Card_Inserted = 1;
    #10 Acc_Number = 4; Card_Inserted = 0;
    #10 Language = 1;
    #10 Password = 'b1;
    #10 Password = 'b0010_0001_0111_1110;
    #10 Password = 'b0010_0101_1001_0000;
    #10 Operation = 2;
    #30;

    //client 1 : password right -> inactive
    #10 Card_Inserted = 1;
    #10 Acc_Number = 0; Card_Inserted = 0;
    #10 Language = 1;
    #30;
    
    //client 3 :  password right -> change password -> new password -> 8998
    #10 Card_Inserted = 1;
    #10 Acc_Number = 2; Card_Inserted = 0;
    #10 Language = 1;
    #10 Password = 'b0001001010110110;
    #10 Operation = 3;
    #10 Password = 'd8998;
    #30; 

    //clent 3 : password wrong -> password wrong -> password wrong -> password wrong -> password wrong -> inactive
    #10 Card_Inserted = 1;
    #10 Acc_Number = 2; Card_Inserted = 0;
    #10 Language = 1;
    #10 Password = 'b1;
    #30;
    #30;

    //client 4 : password right -> dwithdraw = 9000 -> balance = 8143 -> insufficient
    #10 Card_Inserted = 1;
    #10 Acc_Number = 3;  Card_Inserted = 0;
    #10 Language = 1;
    #10 Password = 'b0010_0001_0111_1110;
    #10 Operation = 'b0;
    #10 Cash_Amount = 9000;
    #30;

    #30 $stop;
  end

  // clock generation
  always #5 clk = ~clk;

  //assertions
property insert_card;
        @(posedge clk) disable iff (~rst)
        $rose(Card_Inserted)|=> (DUT.u_Control_Unit.Current_State);
endproperty

property new_password;
        @(posedge clk) disable iff (~rst)
        $rose(DUT.u_Control_Unit.Out_Write_Password_En) |=> (DUT.u_RAM.Accounts[Acc_Number][PASSWORD_WIDTH+BALANCE_WIDTH-1:PASSWORD_WIDTH+BALANCE_WIDTH-16]!= 
        $past(DUT.u_RAM.Accounts[Acc_Number][PASSWORD_WIDTH+BALANCE_WIDTH-1:PASSWORD_WIDTH+BALANCE_WIDTH-16]));
endproperty


property deactivating_account;
  @(posedge clk)
    ((DUT.u_Control_Unit.Current_State == 'b0010) && (DUT.u_Control_Unit.In_Keypad_Password != DUT.u_Control_Unit.In_Account_Passward)) [*NUM_OF_TRIES] |=> ##[1:3] 
    (DUT.u_RAM.Accounts[Acc_Number][0] != $past(DUT.u_RAM.Accounts[Acc_Number][0])) ;
endproperty


property balance_update;
  @(posedge clk) disable iff(!rst)
   (DUT.u_Control_Unit.Current_State == 'b0111) || (DUT.u_Control_Unit.Current_State == 'b0101) |-> ##1
    $changed((DUT.u_RAM.Accounts[DUT.u_RAM.In_Address]));
endproperty

property with_draw_more_than_balance;
  @(posedge clk) disable iff(!rst)
   (DUT.u_Control_Unit.Current_State == 'b0101) |-> (Cash_Amount <= DUT.u_RAM.Out_Re_Balance);
endproperty

CARD_INSERT_ASSERT : assert property (insert_card);
NEW_PASSWORD_ASSERT :assert property (new_password);
DEACTIVATE_ASSERT : assert property (deactivating_account);
BALANCE_UPDATE_ASSERT : assert property (balance_update);
WITH_DRAW_ERROR_ASSERT : assert property (with_draw_more_than_balance);
  //bind assertions file

  //bind ATM_tb ATM_assertions DUT (clk, rst, Card_Inserted, Acc_Number, Language, Password, Operation, Another_Operation_Button, Cash_Amount, Money_Counter_Valid, Money_Counter_Amount)
endmodule
