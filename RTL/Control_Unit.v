module Control_Unit #(
    parameter NUM_OF_STATES='d11,NUM_OF_STATES_WIDTH=$clog2(NUM_OF_STATES),
              NUM_SUPPORTED_LANGUAGES='d3 , NUM_SUPPORTED_LANGUAGES_WIDTH=$clog2(NUM_SUPPORTED_LANGUAGES),
              PASSWORD_WIDTH='d16 ,BALANCE_WIDTH='d16,
              NUM_OF_TRIES='d3 ,NUM_OF_TRIES_WIDTH=$clog2(NUM_OF_TRIES),
              NUM_OF_OPERATION='d4 , NUM_OF_OPERATION_WIDTH=$clog2(NUM_OF_OPERATION)

) (
    input  wire  clk,
    input  wire  RST,

    input  wire                                      In_Start           ,
    input  wire [NUM_SUPPORTED_LANGUAGES_WIDTH-1:0]  In_Language        ,
    input  wire [PASSWORD_WIDTH-1:0]                 In_Keypad_Password ,//! 
    input  wire [BALANCE_WIDTH-1:0]                  In_Keypad_Balance  ,//! 
    input  wire [NUM_OF_OPERATION_WIDTH-1:0]         Operation_Selection,
    input  wire                                      In_Another_Operation_Wanted,

    
    //RAM Interface
    input   wire [PASSWORD_WIDTH-1:0] In_Account_Passward, // ACCOUNT Password Stored in RAM 
    input   wire [BALANCE_WIDTH-1:0]  In_Account_Balance, // ACCOUNT Balance Stored in RAM
    input   wire                      Account_Status,
    output  reg                       Out_Write_Password_En,
    output  reg                       Out_Write_Balance_En,
    output  reg                       Out_Write_Account_Valid_En,
    output  reg [PASSWORD_WIDTH-1:0]  Out_Wr_Password,
    output  reg [BALANCE_WIDTH-1:0]   Out_Wr_Balance,
    output  reg                       Out_Wr_Account_Valid,

    //Money Counter
    output  reg                      Out_Money_Drawer_En,

    input   wire                     In_Money_Counter_Valid  ,
    input   wire [BALANCE_WIDTH-1:0] In_Money_Counter_Amount




);
reg Save_Languages_Selection;
reg [NUM_SUPPORTED_LANGUAGES_WIDTH-1:0] Saved_Language;

reg [NUM_OF_TRIES_WIDTH-1:0] Counter;
reg Counter_Load,Counter_Dec;
wire Counter_Flag;

reg [NUM_OF_STATES_WIDTH-1:0] Current_State,Next_State;

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

always @(posedge clk or negedge RST) begin
    if (!RST) begin
        Current_State<=Idle;
    end else begin
        Current_State<=Next_State;
    end
end

always @(*) begin
    Save_Languages_Selection='b0;

    Counter_Load='b0;
    Counter_Dec='b0;

    Out_Wr_Account_Valid='b0;

    Out_Money_Drawer_En='b0;
    Out_Write_Balance_En='b0;
    Out_Wr_Balance='b0;

    Out_Write_Password_En='b0;
    Out_Wr_Password='b0;

    Out_Write_Account_Valid_En='b0;

    case (Current_State)
        Idle:begin
            if (In_Start) begin
                Next_State=Status_Check;
                //!Out_Timer_En='b1;
                //!Out_Timer_Initial='d500;
            end else begin
                Next_State=Idle;
            end
        end
        //************************************************************************************/
        Status_Check:begin
            if (Account_Status) begin
                Next_State=Language_Select;
            end else begin
                Next_State=Idle;
                //!s$display("Your Account is in-active , please call customer service ");
            end
        end 
        //************************************************************************************/
        Language_Select:begin
            if (~|In_Language) begin
                Next_State=Language_Select;
            end else begin
                Next_State=Inserting_Password;
                Counter_Load='b1;
                Save_Languages_Selection='b1;
            end
        end
        //************************************************************************************/
        Inserting_Password:begin
            if (In_Keypad_Password == In_Account_Passward) begin
                Next_State=Operation_Options;
            end else if (Counter_Flag) begin
                Next_State=DeActivate_Account; //! I Don't think this state is needed
            end else begin
                Next_State=Inserting_Password;
                Counter_Dec='b1;
            end
        end
        //************************************************************************************/
        DeActivate_Account:begin
            Out_Wr_Account_Valid='b0;
            Out_Write_Account_Valid_En='b1;
            Next_State=Idle;
        end
        //************************************************************************************/
        Operation_Options:begin
            case (Operation_Selection)
                'd0: begin
                    Next_State=Withdraw;
                end
                'd1:begin
                    Next_State=Deposit;
                end
                'd2:begin
                    Next_State=Balance_Display;
                end
                'd3:begin
                    Next_State=Change_Password;
                end
                default: Next_State=Idle;
            endcase
        end
        //************************************************************************************/
        Withdraw:begin
            if (In_Keypad_Balance <= In_Account_Balance ) begin
                Out_Money_Drawer_En='b1;
                Out_Write_Balance_En='b1;
                Out_Wr_Balance=In_Account_Balance-In_Keypad_Balance; //!
                Next_State=Balance_Display;
            end else begin
                Next_State = Balance_Display; 
                $display("Insufficient balance"); //!
            end
        end
        //************************************************************************************/
        Deposit:begin
            if (In_Money_Counter_Valid) begin
                Out_Write_Balance_En='b1;
                Out_Wr_Balance=In_Account_Balance+In_Money_Counter_Amount;
                Next_State = Balance_Display;
            end else begin
                Next_State=Deposit;
            end
        end
        //************************************************************************************/
        Change_Password:begin
            Out_Write_Password_En='b1;
            Out_Wr_Password=In_Keypad_Password;
            Next_State=Another_Operation;
        end
        //************************************************************************************/
        Balance_Display:begin
            $display("Your Balance is  %d",In_Account_Balance);
            Next_State=Another_Operation;
        end
        //************************************************************************************/
        Another_Operation:begin
            if(In_Another_Operation_Wanted)begin
                Next_State=Operation_Options;
            end else begin
                Next_State=Idle;
            end
        end
        //************************************************************************************/
        default: begin
            Next_State=Idle;
        end
    endcase
end
    always @(posedge clk or negedge RST) begin
        if (!RST) begin
            Saved_Language='b0;
        end else if(Save_Languages_Selection) begin
            Saved_Language=In_Language;
        end
    end

    always @(posedge clk or negedge RST) begin
        if (!RST) begin
            Counter<=NUM_OF_TRIES-1;
        end else if(Counter_Load) begin
            Counter<=NUM_OF_TRIES-1;
        end else if (Counter_Dec)begin
            Counter<=Counter -1'b1;
        end
    end
    assign Counter_Flag=(Counter=='b0);
endmodule