clc;
clear all;

fileID1 = fopen(['reference_model.txt'],'w');
fileID2 = fopen(['Client_Table_format.txt'],'W');
fileID3 = fopen(['final_output.txt'],'w');
fileID4 = fopen(['final_output_table.txt'],'w');



%% Initializing the system
% Create an array of structures to store client information

for i = 1 : 10
   clients(i).acc_no = randi([0 1000],1,1); % account number
   clients(i).password = randi([1000 9999],1,1); % password
   clients(i).balance = randi([0 10000],1,1); % balance
   clients(i).status = randi([0 1],1,1); % active status
   fprintf(fileID1,'%s%s%s\n',dec2bin(clients(i).password,16),dec2bin(clients(i).balance,16),dec2bin(clients(i).status,1));
   fprintf(fileID2,'%s %s %s\n',dec2bin(clients(i).password,16),dec2bin(clients(i).balance,16),dec2bin(clients(i).status,1));
end





Num_Of_Tries = 5;

while 1
%% Card Handling
% Assume that the card is inserted and account number is received as an input
%% Language Select
disp('Please select language:');
fprintf('\n');
disp('???? :1');
disp('2: English');
language = input('choose langauge ');

X = 0 ;
	
	acc_no = input('enter your account number ');

%% Checking Account Status
client_index = -1;
% Find the client with the matching account number
for i = 1:length(clients)
    if clients(i).acc_no == acc_no
        client_index = i;
        break ;
    end
end

if client_index == -1
        disp('Your account is not found. Please contact the bank.');
        fprintf('\n');
        continue ;
end

% Check if the account is active
if clients(client_index).status == 0
    disp('Your account is inactive. Please contact the bank.');
   fprintf('\n');
    continue;
end


% Assume that the language is selected and the password is received as an input
password = input('enter your account password ');

%% Checking Password
% Set the initial number of tries
tries = 0;

while password ~= clients(client_index).password
    tries = tries + 1;
    
    if tries == Num_Of_Tries
        clients(client_index).status = 0; % change account status to inactive
        disp('Your account is now inactive. Please contact the bank.');
       fprintf('\n');
        X = -1 ;
        break;
    end
    
    password = input('Wrong password. Please try again: ');
end

if X == -1 
    continue ;
end

%% Operation Menu
% Start the timer
tic;
operation = -1 ;
while operation ~= 4
% Show the operation menu
disp('Please select an operation:');
disp('0: Withdraw');
disp('1: Deposit');
disp('2: Balance Services');
disp('3: Change Password');
disp('4: Exit');
fprintf('\n');

% Assume that the operation is selected and the amount is received as an input
operation = input('enter the desired operation '); % for demonstration purposes

%% Perform Operation
switch operation
    case 0 % Withdraw
        amount = input('enter the money amount ');
        if amount > clients(client_index).balance
            disp('Insufficient balance. Please enter a different amount.');
            fprintf('\n');
            disp(['your balance: ' num2str(clients(client_index).balance)]);
           fprintf('\n');
        else   
        clients(client_index).balance = clients(client_index).balance - amount;
        disp(['Remaining balance: ' num2str(clients(client_index).balance)]);
        fprintf('\n');
        end
    case 1 % Deposit
        amount = input('enter the money amount ');
        clients(client_index).balance = clients(client_index).balance + amount;
        disp(['Remaining balance: ' num2str(clients(client_index).balance)]);
        fprintf('\n');
        
    case 2 % Balance Services
        disp(['Current balance: ' num2str(clients(client_index).balance)]);
       fprintf('\n');
        
    case 3 % Change Password
        new_password = input('Please enter your new password: ');
        clients(client_index).password = new_password;
        disp('Password changed successfully.');
       fprintf('\n');
    
    case 4 %  Exit
        break ;
        
    otherwise
        disp('Invalid operation.');
        fprintf('\n');
end

end
        
end

% %% Check Timer
% % Check if the timer has exceeded the maximum time
% if toc > 5*60
%     disp('Maximum time exceeded. Please insert your card again.');
%     break;
% end

for i = 1 : 10
   clients(i).acc_no = randi([0 1000],1,1); % account number
   clients(i).password = randi([1000 9999],1,1); % password
   clients(i).balance = randi([0 10000],1,1); % balance
   clients(i).status = randi([0 1],1,1); % active status
   fprintf(fileID3,'%s%s%s\n',dec2bin(clients(i).password,16),dec2bin(clients(i).balance,16),dec2bin(clients(i).status,1));
   fprintf(fileID4,'%s %s %s\n',dec2bin(clients(i).password,16),dec2bin(clients(i).balance,16),dec2bin(clients(i).status,1));
end

fclose(fileID1);
fclose(fileID2);
fclose(fileID3);
fclose(fileID4);
