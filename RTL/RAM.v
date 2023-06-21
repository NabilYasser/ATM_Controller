module RAM #(
    parameter SAVED_ACCOUNTS='d10 ,ACCOUNT_NUMBER_WIDTH=$clog2(SAVED_ACCOUNTS),
    PASSWORD_WIDTH='d16 ,BALANCE_WIDTH='d16 // Q14.2
) (
    input   wire  clk,
    input   wire  RST,
 
    input   wire [ACCOUNT_NUMBER_WIDTH-1:0] In_Address,

    output  wire [PASSWORD_WIDTH-1:0] Out_Re_Password,
    output  wire [BALANCE_WIDTH-1:0]  Out_Re_Balance,
    output  wire                      Out_Re_Account_Valid,

    
    input  wire  In_Write_Password_En,
    input  wire  In_Write_Balance_En,
    input  wire  In_Write_Account_Valid_En,
    input  wire [PASSWORD_WIDTH-1:0] In_Wr_Password,
    input  wire [BALANCE_WIDTH-1:0]  In_Wr_Balance,
    input  wire                      In_Wr_Account_Valid

);
integer i;
reg [PASSWORD_WIDTH+BALANCE_WIDTH:0] Accounts [0:SAVED_ACCOUNTS-1]; // 16 Bit for password Accounts[end:end-16] +16 bits for balance + 1 valid bit

always @(posedge clk or negedge RST) begin
    if (!RST) begin
        $readmemb("reference_model.txt", Accounts);
    end else if (In_Write_Password_En) begin
        Accounts[In_Address] [PASSWORD_WIDTH+BALANCE_WIDTH:PASSWORD_WIDTH+BALANCE_WIDTH-15] <= In_Wr_Password;
    end else if (In_Write_Balance_En) begin
       Accounts[In_Address] [PASSWORD_WIDTH+BALANCE_WIDTH-16:1] <= In_Wr_Balance;
    end else if (In_Write_Account_Valid_En)begin
        Accounts[In_Address] [0] <= In_Wr_Account_Valid;
    end
end
    assign Out_Re_Password = Accounts[In_Address] [PASSWORD_WIDTH+BALANCE_WIDTH:PASSWORD_WIDTH+BALANCE_WIDTH-15];
    assign Out_Re_Balance = Accounts[In_Address] [PASSWORD_WIDTH+BALANCE_WIDTH-16:1];
    assign Out_Re_Account_Valid = Accounts[In_Address] [0];
endmodule