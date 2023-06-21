class myclass 
#( byte     NUM_OF_STATES='d11,             NUM_OF_STATES_WIDTH=$clog2(NUM_OF_STATES),
   byte     NUM_SUPPORTED_LANGUAGES='d3 ,   NUM_SUPPORTED_LANGUAGES_WIDTH=$clog2(NUM_SUPPORTED_LANGUAGES),
   byte     PASSWORD_WIDTH='d16, 
   byte     BALANCE_WIDTH='d16,
   byte     NUM_OF_TRIES='d3 ,              NUM_OF_TRIES_WIDTH=$clog2(NUM_OF_TRIES),
   byte      NUM_OF_OPERATION='d4 ,         NUM_OF_OPERATION_WIDTH=$clog2(NUM_OF_OPERATION),
   byte     SAVED_ACCOUNTS='d6 ,          ACCOUNT_NUMBER_WIDTH=$clog2(SAVED_ACCOUNTS)
);
  rand  bit                                             Card_Valid; // Start Signal
  rand  bit         [ACCOUNT_NUMBER_WIDTH-1:0]          Card_Number;
  rand  bit         [1:0] Language;
  rand  bit         [BALANCE_WIDTH-1:0]                 KeyPad_Balance;
  rand  bit         [PASSWORD_WIDTH-1:0]                KeyPad_Password;
  rand  bit         [NUM_OF_OPERATION_WIDTH-1:0]        Operation_Selection;
  rand  bit                                             In_Another_Operation_Wanted;
  rand  bit                                             Money_Counter_Valid  ;
  rand  bit         [BALANCE_WIDTH-1:0]                 Money_Counter_Amount ;

  //constraints
  constraint  const1  {Language dist { [1:2]:/95, 3:/0, 0:/0};  }


endclass


module randomization();
    initial 
    begin
        
      for(int i = 0; i < 10; i++  )
        begin
           automatic myclass cls = new();
            cls.randomize(); 
            $display("itr= %d Language = %d\n",i,cls.Language);
            $display("itr= %d card_valid = %d\n",i,cls.Card_Valid);
        end
    end


endmodule