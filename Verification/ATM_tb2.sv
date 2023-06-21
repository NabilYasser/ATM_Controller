`timescale 1ns/1ps


class passwordclass#(byte  PASSWORD_WIDTH ='d16);
  rand  bit         [PASSWORD_WIDTH-1:0]         KeyPad_Password;
  constraint  const3  {KeyPad_Password inside { 'b0001000001100011,
                                                'b0001100100101100,
                                                'b0001001010110110,
                                                'b0010000101111110,
                                                'b0010010110010000,
                                                'b0001000100001010,
                                                'b0000010101111101,
                                                'b0001000101100110,
                                                'b0010000000001101,
                                                'b0001100110011011};}
endclass

class myclass 
#( byte     NUM_OF_STATES='d11,             NUM_OF_STATES_WIDTH=$clog2(NUM_OF_STATES),
   byte     NUM_SUPPORTED_LANGUAGES='d3 ,   NUM_SUPPORTED_LANGUAGES_WIDTH=$clog2(NUM_SUPPORTED_LANGUAGES),
   byte     PASSWORD_WIDTH='d16, 
   byte     BALANCE_WIDTH='d16,
   byte     NUM_OF_TRIES='d3 ,              NUM_OF_TRIES_WIDTH=$clog2(NUM_OF_TRIES),
   byte      NUM_OF_OPERATION='d4 ,         NUM_OF_OPERATION_WIDTH=$clog2(NUM_OF_OPERATION),
   byte     SAVED_ACCOUNTS='d10 ,          ACCOUNT_NUMBER_WIDTH=$clog2(SAVED_ACCOUNTS)
);
  randc  bit                                             Card_Valid; // Start Signal
  randc  bit         [ACCOUNT_NUMBER_WIDTH-1:0]          Card_Number;
  randc  bit         [1:0]                               Language;
  randc  bit         [BALANCE_WIDTH-1:0]                 KeyPad_Balance;
  //randc  bit         [PASSWORD_WIDTH-1:0]                KeyPad_Password;
  randc  bit         [NUM_OF_OPERATION_WIDTH-1:0]        Operation_Selection;
  randc  bit                                             In_Another_Operation_Wanted;
  randc  bit                                             Money_Counter_Valid  ;
  randc  bit         [BALANCE_WIDTH-1:0]                 Money_Counter_Amount ;

  //constraints
  constraint  const1  {Language dist { [1:2]:/95, 3:/0, 0:/0};  }
  constraint  const2  {Money_Counter_Valid dist {1:/100, 0:/0};  }
  constraint  const3  {In_Another_Operation_Wanted dist {0:/100, 0:/0};}
  constraint  const4  {Card_Valid dist {1:/100, 0:/0};}
  constraint  const5  {Card_Number inside {[0:9]};}

endclass

module ATM_tb2 #(
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
    .clk                                    (clk),
    .RST                                    (rst),
    .Card_Valid                             (Card_Inserted),
    .Card_Number                            (Acc_Number),
    .Language                               (Language),
    .KeyPad_Balance                         (Cash_Amount), //used in withdrawing the money
    .KeyPad_Password                        (Password),
    .Operation_Selection                    (Operation),
    .Money_Counter_Valid                    (Money_Counter_Valid),
    .Money_Counter_Amount                   (Money_Counter_Amount), //used in depositing money in account
    .In_Another_Operation_Wanted            (Another_Operation_Button),
    .Money_Drawer_En                        (Money_Drawer_En)
  );

// clock generator

always #5 clk = ~clk;


// reset generator
initial
     begin
        clk = 0;
        rst = 0;
        #10 rst = 1;
    end

//----------------------Coverage-------------------------//
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
covergroup address @(posedge clk);
   cover_point_address: coverpoint Acc_Number {
    bins Valid_addresses[] = {[0:9]};
    illegal_bins invalid_addresses [] = {[10:15]};
   }
endgroup
address S2;


initial 
      begin
    S1 = new(ATM_tb2.DUT.u_Control_Unit.Current_State);
    S2 = new();
    #10;
      for(int i = 0; i < 30; i++)
        begin
           automatic myclass cls = new();
           cls.randomize(); 
          
            Card_Inserted = 1; 
            Acc_Number = cls.Card_Number;
            Language = cls.Language;
            Cash_Amount = cls.KeyPad_Balance;
            //Password = cls1.KeyPad_Password;                       //DUT.u_RAM.Accounts[Acc_Number][PASSWORD_WIDTH+BALANCE_WIDTH:PASSWORD_WIDTH+BALANCE_WIDTH-15];
            Operation = cls.Operation_Selection;


            if ( i == 2)
              Another_Operation_Button = 1;    
            else    
              Another_Operation_Button = 0; 


            Money_Counter_Valid =  1;                            
            Money_Counter_Amount = cls.Money_Counter_Amount ;

            #10
            if(Card_Inserted == 1'b1)
            begin
                    Card_Inserted = 0;
            end
            
            #20
            for ( int j = 0; j < NUM_OF_TRIES; j++)
            begin
                    if(DUT.u_Control_Unit.Current_State == 'b0010)   // inserting password
                        begin
                          automatic passwordclass cls1 = new();
                          cls1.randomize();
                          Password = cls1.KeyPad_Password;
                        end
                    else
                      break;
                #10;
            end

            #20
            if(DUT.u_Control_Unit.Current_State == 'b1111)   //new password
              begin
                          Password = $random();
              end

           /* $display("itr= %d\t card_valid = %d \n Card_Number = %d\t Language = %d\n 
                      Cash_Amount= %d\t Password= %d \n Operation= %d\t Another_Operation_Button= %d\t Money_Counter_Valid= 
                      %d  Money_Counter_Amount = %d",i, Card_Inserted, Acc_Number, Language, Cash_Amount, 
                      Password, Operation, Another_Operation_Button, Money_Counter_Valid, Money_Counter_Amount);*/
            #100;
            

        end
        $stop;
    end

    always @(posedge clk) begin
      if(DUT.u_Control_Unit.Current_State == 'b0010)   // inserting password
                        begin
                          automatic passwordclass cls1 = new();
                          cls1.randomize();
                          Password = cls1.KeyPad_Password;
                          #10;
                        end
    end

 //----------sequence declaration-----------//
sequence confirm_withdraw;
(DUT.u_Control_Unit.In_Keypad_Balance <= DUT.u_Control_Unit.In_Account_Balance) && (DUT.u_Control_Unit.Current_State == 'b0101);
endsequence

sequence confirm_deposite;
(DUT.u_Control_Unit.Current_State == 'b0111) &&(DUT.u_Control_Unit.In_Money_Counter_Valid);
endsequence

   //assertions
property insert_card;
        @(posedge clk) disable iff (~rst)
        $rose(Card_Inserted)|=> (DUT.u_Control_Unit.Current_State);
endproperty

property new_password;
        @(posedge clk) disable iff (~rst)
        $rose(DUT.u_Control_Unit.Out_Write_Password_En) |=> (DUT.u_RAM.Accounts[Acc_Number][PASSWORD_WIDTH+BALANCE_WIDTH:PASSWORD_WIDTH+BALANCE_WIDTH-15]!= 
        $past( DUT.u_RAM.Accounts[Acc_Number][PASSWORD_WIDTH+BALANCE_WIDTH:PASSWORD_WIDTH+BALANCE_WIDTH-15]));
endproperty


property deactivating_account;
  @(posedge clk)
    ((DUT.u_Control_Unit.Current_State == 'b0010) && (DUT.u_Control_Unit.In_Keypad_Password != DUT.u_Control_Unit.In_Account_Passward)) [*NUM_OF_TRIES] |=> ##[1:3] 
    (DUT.u_RAM.Accounts[Acc_Number][0] != $past(DUT.u_RAM.Accounts[Acc_Number][0])) ;
endproperty


property balance_update_deposite;
  @(posedge clk) disable iff(!rst)
   confirm_deposite |=>
   $changed((DUT.u_RAM.Accounts[DUT.u_RAM.In_Address]));
endproperty

property balance_update_withdraw;
  @(posedge clk) disable iff(!rst)
   confirm_withdraw |=>
   $changed((DUT.u_RAM.Accounts[DUT.u_RAM.In_Address]));
endproperty

property with_draw_more_than_balance;
  @(posedge clk) disable iff(!rst)
   (DUT.u_Control_Unit.Current_State == 'b0101) |-> (Cash_Amount <= DUT.u_RAM.Out_Re_Balance);
endproperty

CARD_INSERT_ASSERT : assert property (insert_card);
NEW_PASSWORD_ASSERT :assert property (new_password);
DEACTIVATE_ASSERT : assert property (deactivating_account);
BALANCE_UPDATE_DEPOSITE_ASSERT: assert property (balance_update_deposite);
BALANCE_UPDATE_WITHDRAW_ASSERT: assert property (balance_update_withdraw);
WITH_DRAW_ERROR_ASSERT : assert property (with_draw_more_than_balance);  

endmodule
