`timescale 1ns/1ps

module ATM_cover_tb #(
    parameter   NUM_OF_STATES='d11,                             NUM_OF_STATES_WIDTH=$clog2(NUM_OF_STATES),
                NUM_SUPPORTED_LANGUAGES='d4 ,                   NUM_SUPPORTED_LANGUAGES_WIDTH=$clog2(NUM_SUPPORTED_LANGUAGES),
                NUM_OF_TRIES='d3 ,                              NUM_OF_TRIES_WIDTH=$clog2(NUM_OF_TRIES),
                NUM_OF_OPERATION='d4 ,                          NUM_OF_OPERATION_WIDTH=$clog2(NUM_OF_OPERATION),
                SAVED_ACCOUNTS='d10 ,                           ACCOUNT_NUMBER_WIDTH=$clog2(SAVED_ACCOUNTS),
                PASSWORD_WIDTH='d16 ,                           BALANCE_WIDTH='d16
);


localparam [NUM_OF_STATES_WIDTH-1:0] Idle='b0000 ,
                                     Status_Check='b0001,
                                     Language_Select='b0011,
                                     Inserting_Password='b0010,
                                     DeActivate_Account='b0110,//!
                                     Operation_Options='b0100,
                                     Withdraw='b0101,
                                     Deposit='b0111,
                                     Change_Password='b1111,
                                     Balance_Display='b1110,
                                     Another_Operation='b1100;


  // Inputs
  reg clk;
  reg rst;
  reg Card_Inserted;
  reg [ACCOUNT_NUMBER_WIDTH-1:0] Acc_Number;
  reg [NUM_SUPPORTED_LANGUAGES_WIDTH-1:0] Language;
  reg [PASSWORD_WIDTH-1:0] Password;
  reg [NUM_OF_OPERATION_WIDTH-1:0] Operation;
  reg Another_Operation_Button;
  reg [BALANCE_WIDTH-1:0] Cash_Amount ;
  reg Money_Counter_Valid;
  reg [BALANCE_WIDTH-1:0] Money_Counter_Amount;
  wire Money_Drawer_En;



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

//---------------covergroup-----------//
covergroup state_transition (ref reg [NUM_OF_STATES_WIDTH-1:0] current_state) @(posedge clk);
  cover_point_states: coverpoint current_state {
bins VALID_STATE[] =  {Idle, Status_Check, Language_Select, Inserting_Password, 
                      DeActivate_Account, Operation_Options, Withdraw, Deposit, 
                      Change_Password, Balance_Display, Another_Operation};
bins INACTIVE_ACCOUNT = (Idle => Status_Check => Idle);
bins DE_ACTIVATION = (Idle => Status_Check => Language_Select => Inserting_Password [*1:NUM_OF_TRIES] => DeActivate_Account => Idle);
bins WITHDRAWING = (Idle => Status_Check => Language_Select => Inserting_Password [*1:NUM_OF_TRIES] => Operation_Options => Withdraw => Balance_Display => Another_Operation => Idle);
bins DEPOSITING = (Idle => Status_Check => Language_Select => Inserting_Password [*1:NUM_OF_TRIES] =>  Operation_Options => Deposit => Balance_Display => Another_Operation => Idle);
bins BALANCE_DISPLAYING = (Idle => Status_Check => Language_Select => Inserting_Password [*1:NUM_OF_TRIES]  => Operation_Options => Balance_Display => Another_Operation => Idle);
bins CHANGING_PASSWORD = (Idle => Status_Check => Language_Select => Inserting_Password [*1:NUM_OF_TRIES]  => Operation_Options => Change_Password => Another_Operation => Idle);
}
endgroup



state_transition S1;

  initial begin
  
   
    S1 = new(ATM_cover_tb.DUT.u_Control_Unit.Current_State);

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
    #(NUM_OF_TRIES*10);
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
 //----------sequence declaration-----------//
sequence confirm_withdraw;
(DUT.u_Control_Unit.In_Keypad_Balance <= DUT.u_Control_Unit.In_Account_Balance) && (DUT.u_Control_Unit.Current_State == 'b0101);
endsequence

sequence confirm_deposite;
(DUT.u_Control_Unit.Current_State == 'b0111) &&(DUT.u_Control_Unit.In_Money_Counter_Valid);
endsequence

//-----------property declaration------------//
property insert_card;
  @(posedge clk)
      Card_Inserted |=> (DUT.u_Control_Unit.Current_State);
endproperty
 
property deactivating_account;
  @(posedge clk)
    (DUT.u_Control_Unit.Current_State == 'b0010) && (DUT.u_Control_Unit.In_Keypad_Password != DUT.u_Control_Unit.In_Account_Passward) [*NUM_OF_TRIES] |=> ##[1:3]
    $changed((DUT.u_RAM.Accounts[DUT.u_RAM.In_Address][0]));
    //(DUT.u_RAM.Accounts[DUT.u_RAM.In_Address][0] != $past(DUT.u_RAM.Accounts[DUT.u_RAM.In_Address][0])) ;
endproperty

property balance_update_deposite;
  @(posedge clk) disable iff(!rst)
   confirm_deposite |=>
   $changed((DUT.u_RAM.Accounts[DUT.u_RAM.In_Address]));
endproperty

property balance_update_withdraw;
  @(posedge clk) disable iff(!rst)
   confirm_deposite |=>
   $changed((DUT.u_RAM.Accounts[DUT.u_RAM.In_Address]));
endproperty
//-----assertion declaration---------------//
INSERT_CARD_ASSERT: assert property (insert_card);
DEACTIVATE_ASSERT: assert property (deactivating_account);
BALANCE_UPDATE_DEPOSITE_ASSERT: assert property (balance_update_deposite);
BALANCE_UPDATE_WITHDRAW_ASSERT: assert property (balance_update_withdraw);



endmodule
