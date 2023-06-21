module ATM #(
    parameter NUM_OF_STATES='d11,NUM_OF_STATES_WIDTH=$clog2(NUM_OF_STATES),
              NUM_SUPPORTED_LANGUAGES='d3 , NUM_SUPPORTED_LANGUAGES_WIDTH=$clog2(NUM_SUPPORTED_LANGUAGES),
              PASSWORD_WIDTH='d16 ,BALANCE_WIDTH='d16,
              NUM_OF_TRIES='d3 ,NUM_OF_TRIES_WIDTH=$clog2(NUM_OF_TRIES),
              NUM_OF_OPERATION='d4 , NUM_OF_OPERATION_WIDTH=$clog2(NUM_OF_OPERATION),
              SAVED_ACCOUNTS='d10 ,ACCOUNT_NUMBER_WIDTH=$clog2(SAVED_ACCOUNTS)
) (
    input  wire  clk,
    input  wire  RST,
    input  wire  Card_Valid, // Start Signal
    input  wire [ACCOUNT_NUMBER_WIDTH-1:0] Card_Number,
    input  wire  [NUM_SUPPORTED_LANGUAGES_WIDTH-1:0] Language,
    input  wire  [BALANCE_WIDTH-1:0]  KeyPad_Balance,
    input  wire  [PASSWORD_WIDTH-1:0] KeyPad_Password,
    input  wire  [NUM_OF_OPERATION_WIDTH-1:0] Operation_Selection,
    input  wire  In_Another_Operation_Wanted,
    input   wire                     Money_Counter_Valid  ,
    input   wire [BALANCE_WIDTH-1:0] Money_Counter_Amount ,
    output wire  Money_Drawer_En

);
wire [PASSWORD_WIDTH-1:0] Account_Passward,Wr_Password;
wire [BALANCE_WIDTH-1:0]  Account_Balance,Wr_Balance;
wire Account_Status,Wr_Account_Valid;
wire Write_Password_En ,Write_Balance_En ,Write_Account_Valid_En;

RAM #(
    .SAVED_ACCOUNTS       (SAVED_ACCOUNTS       ),
    .ACCOUNT_NUMBER_WIDTH (ACCOUNT_NUMBER_WIDTH ),
    .PASSWORD_WIDTH       (PASSWORD_WIDTH       ),
    .BALANCE_WIDTH        (BALANCE_WIDTH        )
)
u_RAM(
    .clk                       (clk                       ),
    .RST                       (RST                       ),
    .In_Address                (Card_Number               ),
    .Out_Re_Password           (Account_Passward          ),
    .Out_Re_Balance            (Account_Balance           ),
    .Out_Re_Account_Valid      (Account_Status          ),
    .In_Write_Password_En      (Write_Password_En         ),
    .In_Write_Balance_En       (Write_Balance_En          ),
    .In_Write_Account_Valid_En (Write_Account_Valid_En    ),
    .In_Wr_Password            (Wr_Password            ),
    .In_Wr_Balance             (Wr_Balance             ),
    .In_Wr_Account_Valid       (Wr_Account_Valid       )
);



Control_Unit #(
    .NUM_OF_STATES                 (NUM_OF_STATES                 ),
    .NUM_OF_STATES_WIDTH           (NUM_OF_STATES_WIDTH           ),
    .NUM_SUPPORTED_LANGUAGES       (NUM_SUPPORTED_LANGUAGES       ),
    .NUM_SUPPORTED_LANGUAGES_WIDTH (NUM_SUPPORTED_LANGUAGES_WIDTH ),
    .PASSWORD_WIDTH                (PASSWORD_WIDTH                ),
    .BALANCE_WIDTH                 (BALANCE_WIDTH                 ),
    .NUM_OF_TRIES                  (NUM_OF_TRIES                  ),
    .NUM_OF_TRIES_WIDTH            (NUM_OF_TRIES_WIDTH            ),
    .NUM_OF_OPERATION              (NUM_OF_OPERATION              ),
    .NUM_OF_OPERATION_WIDTH        (NUM_OF_OPERATION_WIDTH        )
)
u_Control_Unit(
    .clk                         (clk                         ),
    .RST                         (RST                         ),
    .In_Start                    (Card_Valid                  ),
    .In_Language                 (Language                    ),
    .In_Keypad_Password          (KeyPad_Password             ),
    .In_Keypad_Balance           (KeyPad_Balance              ),
    .Operation_Selection         (Operation_Selection         ),
    .In_Another_Operation_Wanted (In_Another_Operation_Wanted ),
    .In_Account_Passward         (Account_Passward            ),
    .In_Account_Balance          (Account_Balance             ),
    .Account_Status              (Account_Status              ),
    .Out_Write_Password_En       (Write_Password_En           ),
    .Out_Write_Balance_En        (Write_Balance_En            ),
    .Out_Write_Account_Valid_En  (Write_Account_Valid_En      ),
    .Out_Wr_Password             (Wr_Password                 ),
    .Out_Wr_Balance              (Wr_Balance                  ),
    .Out_Wr_Account_Valid        (Wr_Account_Valid            ),
    .Out_Money_Drawer_En         (Money_Drawer_En             ),
    .In_Money_Counter_Valid      (Money_Counter_Valid         ),
    .In_Money_Counter_Amount     (Money_Counter_Amount        )
);

    
endmodule