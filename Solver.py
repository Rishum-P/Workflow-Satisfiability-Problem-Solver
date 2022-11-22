# Rishum - Knowledge Representation and Reasoning - Coursework project
# An OR-Tools solver to solve the Workflow Satisfiability Problem.

import itertools
import re
import sys
import time
from ortools.sat.python import cp_model


# This is the callback class that will be used to help calculate if multiple solutions exist, later in the program.
# It stores the solutions in a list, the stepassignment (mapping between steps & users) variables.
# The call back will terminate after it finds 2 solutions, as we do not need to find more than 2 for this assignment.
class SolutionCallback(cp_model.CpSolverSolutionCallback):

    def __init__(self, variables):
        cp_model.CpSolverSolutionCallback.__init__(self)
        self.__variables = variables
        self.__solution_count = 0
        self.solution_list = []

    def on_solution_callback(self):
        # On every callback, increase solution count.
        self.__solution_count += 1

        # Add the solution to the solution list.
        self.solution_list.append([self.Value(v) for v in self.__variables])

        # If the solution counter is greater than 2, stop the search for more.
        if self.__solution_count >= 2:
            self.StopSearch()

    def solution_count(self):
        # Return the number of solutions.
        return self.__solution_count


# This class is purely used just to store data in a class that can be then accessed.
class Instance:
    def __init__(self):
        self.Steps = 0
        self.Users = 0
        self.Constraints = 0
        self.authorisations
        self.separationofduty
        self.bindingofduty
        self.atmostk
        self.oneteam_teams
        self.oneteam_steps


# Reads the data into the program for use in the solver. Data can either be passed as an argument (compatible with
# coursework tester), by adding a file name in the File_Name variable below, or by entering a file location when the
# program starts.
def Read_Data():
    # File_Name to specify a manual location. Useful if testing with same instance multiple times.
    File_Name = ""
    # File_Name = "instances/example5.txt"

    # If a manual file name is not specified, check if a name is passed in as an argument. If not ask the user for a
    # file location instead.
    args = sys.argv[1:]
    if args:
        File_Name = sys.argv[1]
    elif not File_Name:
        File_Name = input("Enter file location: ")

    # Open the file.
    f = open(File_Name, "r")

    # Read in the number of steps, users and steps. These 3 lines have been taken from the Coursework FAQ
    Instance.Steps = int(re.match(r'#Steps:\s+(\d+)', f.readline(), re.IGNORECASE).group(1))
    Instance.Users = int(re.match(r'#Users:\s+(\d+)', f.readline(), re.IGNORECASE).group(1))
    Instance.Constraints = int(re.match(r'#Constraints:\s+(\d+)', f.readline(), re.IGNORECASE).group(1))

    # Print number of Steps, Users and Constraints.
    print("Steps " + str(Instance.Steps))
    print("Users " + str(Instance.Users))
    print("Constraints " + str(Instance.Constraints))

    # The remaining lines should be the constraints, so read all the lines in.
    lines = f.read().lower().splitlines()

    # Preparing the Instance variables for the type of data it will hold.
    Instance.authorisations = [None] * Instance.Users
    Instance.separationofduty = []
    Instance.bindingofduty = []
    Instance.atmostk = []
    Instance.oneteam_teams = []
    Instance.oneteam_steps = []

    # Loop though each line to handle each constraint individually.
    for line in lines:

        # Reading in a new authorisation constraint
        if "authorisations" in line:

            # Getting which user the authorisation belongs too
            User = re.findall(r'u\d+', line)
            User = User[0][1:]

            # Getting the steps that this user can perform and putting it into a comma delimited string
            Steps_Joined = ""
            for Individual_Step in re.findall('s\d+', line):
                Steps_Joined = Steps_Joined + Individual_Step[1:] + ","

            # Storing it in the list for later use.
            Instance.authorisations[int(User) - 1] = Steps_Joined[:-1]

        # Reading in a new separation-of-duty constraint
        elif "separation-of-duty" in line:

            # This constraint is just contains steps so we can just put it in a comma delimited string and store it.
            SepString = ""
            for seperation in re.findall("s\d+", line):
                SepString = SepString + seperation[1:] + ","
            Instance.separationofduty.append(SepString[:-1])

        # Reading in a new binding-of-duty constraint
        elif "binding-of-duty" in line:

            # This constraint is just contains steps so we can just put it in a comma delimited string and store it.
            BindString = ""
            for binding in re.findall("s\d+", line):
                BindString = BindString + binding[1:] + ","
            Instance.bindingofduty.append(BindString[:-1])

        # Reading in a new at-most-k constraint
        elif "at-most-k" in line:

            # We handle this slightly differently from the other constraints as we will need to access both K and T
            # separately thus we store both of them in a 2d list.
            values = line.split()
            k = int(values[1])
            T = [int(v[1:]) for v in values[2:]]
            Instance.atmostk.append([k, T])

        # Reading in a one-team constraint
        elif "one-team" in line:

            # We first find the Teams and Steps using Regex.
            Teams = re.findall(r'\((.*?)\)', line)
            Steps = re.findall("s\d+", line)

            # Insert all steps into an List
            for Individual_Step in range(len(Steps)):
                Test = re.findall(r'\d+', Steps[Individual_Step])
                Steps[Individual_Step] = Test[0]

            # Insert all teams into an List
            for teams in range(len(Teams)):
                Test = re.findall(r'\d+', Teams[teams])
                Teams[teams] = Test

            # Its little easier to store Teams and Steps separately this time.
            Instance.oneteam_teams.append(Teams)
            Instance.oneteam_steps.append(Steps)


def Solver():
    # Declare the Constraint model
    model = cp_model.CpModel()

    # Declare a list that will represent the mapping between Steps and Users.
    StepAssignment = []

    # Start by giving each step a variable that will be assigned a User. The max size this variable is the number of
    # users.
    for i in range(Instance.Steps):
        StepAssignment.append(model.NewIntVar(0, Instance.Users, 'Step[%i]' % i))

    # Each user that each step is assigned must be in the correct range. E.G. Between 1 and Number of users.
    # E.G. If there are 4 users, the user assigned for step must be between 1 - 4. We cannot assign it 5 or 10.
    for i in range(Instance.Steps):
        model.Add(StepAssignment[i] >= 1)
        model.Add(StepAssignment[i] <= Instance.Users)

    # Constraint 1 - Authorisations. A step must be assigned to a user that is allowed to perform that step.

    # Loop through all the User Authorisations. The index of User_Auths represents the User and stored values at that
    # index represents the steps they are able to perform. If a user (index) is None, then they where assigned no
    # steps and have authorisation to perform them all.
    for User_Auths in range(Instance.Users):

        # Get the steps that the user is allowed to perform.
        Step_Allowed = Instance.authorisations[User_Auths]

        # Loop through each step.
        for Step in range(1, Instance.Steps + 1):

            # Check if the user is assigned no steps, if not we can skip.
            if not Step_Allowed is None:

                # Create a list of the steps allowed for the user.
                Step_List = Step_Allowed.split(",")

                # Search the list and if the current Step is not in the list of steps the user is allowed to perform
                # then add the constraint that that step cannot be assigned to that user to the model.
                if not str(Step) in Step_List:
                    model.Add(StepAssignment[Step - 1] != (User_Auths + 1))

    # Constraint 2 - Separation of duty. Given a list of steps, the users assigned to them cannot be the same.

    # Loop though every index of the separationofduty variable that stores all of the seperation of duty rules.
    for Seperation_Of_Duty_Index in range(len(Instance.separationofduty)):
        # Get the two steps that each Seperation of Duty constraint relates too.
        SeperationOfDuty = Instance.separationofduty[Seperation_Of_Duty_Index]
        SeperationOfDuty_Split = SeperationOfDuty.split(",")

        # Add the user assigned to these steps cannot be equal. E.G. s1 != s4.
        model.Add(
            StepAssignment[int(SeperationOfDuty_Split[0]) - 1] != StepAssignment[int(SeperationOfDuty_Split[1]) - 1])

    # Constraint 3 - Binding of Duty. Given a list of steps, the users assigned to them are the same. This works very
    # similar to the previous constraint just with a == instead of !=.

    # Loop though every index of the bindingofduty variable that stores all of the binding of duty rules.
    for BindingOfDutyIndex in range(len(Instance.bindingofduty)):
        # Get the two steps that each Binding Of Duty constraint relates too.
        BindingOfDuty = Instance.bindingofduty[BindingOfDutyIndex]
        BindingOfDuty_Split = BindingOfDuty.split(",")

        # Add the user assigned to these must be equal. E.G. s2 == s3.
        model.Add(StepAssignment[int(BindingOfDuty_Split[0]) - 1] == StepAssignment[int(BindingOfDuty_Split[1]) - 1])

    # Constraint 4 - At Most K. Given a list of steps and max number of users. The assigned number of users for these
    # steps must not exceed the max not of users.

    # Loop for every value in the atmostk variable that stores the relevant constraints.
    for AtMostK in Instance.atmostk:

        # Get both the value of K (Max number of users) and the relavent steps.
        Steps = AtMostK[1]
        K = AtMostK[0]

        # The code highlighted around the ---- is taken from the following source/paper:
        # Karapetyan, D. and Gutin, G., 2021. Solving the Workflow Satisfiability Problem using General Purpose Solvers. arXiv preprint arXiv:2105.03273.
        # Code for the above reference can be found at: https://rdmc.nottingham.ac.uk/handle/internal/9142
        # -----------------------------------

        # Get each combination of Steps for the length of K
        for Steps_Combinations in itertools.combinations(Steps, K + 1):

            # Create an list that will contain boolean variables.
            IsEqual_Bool = []

            # Get the combinations of combinations but for a length of 2.
            for (Step1, Step2) in itertools.combinations(Steps_Combinations, 2):
                # Create a new var that will be true if Step 1 and 2 are equal.
                Bool_Var = model.NewBoolVar('')

                # If step 1 and 2 are equal then set the boolvar for these steps to true
                model.Add(StepAssignment[Step1 - 1] == StepAssignment[Step2 - 1]).OnlyEnforceIf(Bool_Var)

                # Append this too the list
                IsEqual_Bool.append(Bool_Var)

            # Require at least 1 boolean value to be true.
            model.Add(sum(IsEqual_Bool) >= 1)
        # -----------------------------------

    # Constraint 5 - One Team. For the steps given, they must all be assigned to only users of one of the teams given.

    # Look for the index of every group in the oneteam_teams varable that holds the constraints
    for OneTeam in range(len(Instance.oneteam_teams)):

        # Get the teams and the steps for each One Team constant.
        Steps = Instance.oneteam_steps[OneTeam]
        Teams = Instance.oneteam_teams[OneTeam]

        # Create a list that will contain the relevant variables from step assignment.
        StepsToAdd = []

        # Add the step variables from step assignment to the list. These are the steps that are relevant for this
        # particular constant.
        for s in Steps:
            StepsToAdd.append(StepAssignment[int(s) - 1])

        # This list will hold the allowed combinations of users that will be added to the model.
        Allowed_Combinations = []

        # Loop for every individual team.
        for team in Teams:

            # Will store the cartesian product for each individual team.
            Products_For_Individual_Team = []

            # Find the cartesian product for each team and loop through them all. The number of repeated values
            # need to be equal to the given number of steps in the constraint in order to be the correct format to
            # add to the model.
            for product in itertools.product(team, repeat=len(Steps)):

                # Add each permutation to a list. This is purely to format it correctly.
                Individual_Product = []

                for individual in product:
                    Individual_Product.append(int(individual))

                # For individual cartesian product's add it to the running list of the whole teams cartesian product's
                Products_For_Individual_Team.append(Individual_Product)

            # Add the teams cartesian product's to the list of allowed combinations.
            Allowed_Combinations = Allowed_Combinations + Products_For_Individual_Team

        # Tell the model that only the combinations given in Allowed_Combinations are allowed for the steps given
        # in StepsToAdd
        model.AddAllowedAssignments(StepsToAdd, Allowed_Combinations)

    # Create a new solver.
    solver = cp_model.CpSolver()

    # Pass the steps to the Solution Callback
    solutions = SolutionCallback(StepAssignment)

    # Ensure all solutions are enumerated
    solver.parameters.enumerate_all_solutions = True

    # Start a timer so we can measure how long it takes to solve
    tic = time.perf_counter()

    # Start solving using the model. Pass our callback so we can establish if there are multiple solutions.
    status = solver.Solve(model, solutions)

    # Stop the timer once the model is solved.
    toc = time.perf_counter()

    # If the returned status of the solver is Optimal or Feasiable then we have found at least 1 solution.
    if status == cp_model.OPTIMAL or status == cp_model.FEASIBLE:

        # Print that the problem is satisfiable.
        print("\nsat")

        # At this point we know there is at least 1 solution, so print it out with some formatting.
        Solution = solutions.solution_list[0]
        for i in range(len(Solution)):
            print("s" + str(i + 1) + ": u" + str(Solution[i]))

        # If our call backs solution_count variable is 1, we can print out that this is the only solution.
        if solutions.solution_count() == 1:
            print("\nthis is the only solution")
        else:
            # If however the solution count is > 1 then we need to do more checking. The callback function will
            # terminate after it has found 2 solutions, as this coursework only required us to establish if there is
            # more than 1 solution. However for some reason the solver will in some instances return multiple of the
            # same solution but this only seems to occur if there is actually only 1 solution. In testing i've found
            # that this is related to the AddBoolOr in Constant 4. So a simple fix for this is just to compare if the
            # first solution is equal to the second solution and if it is, there is only 1 solution. We can then
            # print this
            if solutions.solution_list[0] == solutions.solution_list[1]:
                print("\nThis is the only solution")
            else:
                # If however they are not equal then print that multiple solutions exist. As its already been
                # computed I also print the 2nd solution (without formatting as to not break the tester) as there is
                # no harm in doing so.
                print("\nOther solutions exist. Such as: " + str(solutions.solution_list[1]))
    else:
        # If the model is not Optimal or Feasible then return Unsat.
        print("\nUnsat")

    # Print the time taken.
    print(f"Time Taken: ({(toc - tic) * 1000:0.4f}ms) ({(toc - tic):0.4f}s)")


# Once program is run, call ReadData then Solver()
if __name__ == '__main__':
    Read_Data()
    Solver()
