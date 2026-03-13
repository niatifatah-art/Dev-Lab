# This is my first day of learning Python. I am excited to start this journey and learn new things.
#13/03/2026
name = "Fatah"
avg = 9.5/10
age = 20
is_student = True
will_work_in_tech_company = True
print(name)
print(avg)  
print(age)
print(is_student)
print(will_work_in_tech_company)

#exercise 1
# Create a variable called "patient_name" and assign it the value "John Smith".
patient_name = "John Smith"
patient_age = 20
is_a_new_patient = True
print(patient_name)
print(patient_age)
print(is_a_new_patient)

#learning about input function
# The input() function allows you to take user input from the console. When you call input(), the program will pause and wait for the user to type something and press Enter. The value entered by the user will be returned as a string.
name = input("What is your name? ")
print("Hello, " + name + "! Welcome to the world of Python programming!")

#exercise 2
# Create a program that asks the user for their name and their favorite color, and then prints a message saying "Hello [name], your favorite color is [color]!".
name = input("What is your name? ")
favorite_color = input("What is your favorite color? ")
print(name + " likes " + favorite_color)

#lesson 3
# The input() function always returns a string, even if the user enters a number. If you want to use the input as a number, you need to convert it using int() for integers or float() for floating-point numbers.
birth_year = input("Birth year: ")
print(type(birth_year))
age = 2026 - int(birth_year)
print(type(age))
print(age)
 
#exercise 3
# Create a program that asks the user for their weight in pounds and converts it to kilograms. The formula for converting pounds to kilograms is: weight_in_kg = weight_in_pounds / 2.20462.
weight_in_pounds = float(input("What is your weight? "))
weight_in_kg = weight_in_pounds / 2.20462

print("Your weight in pounds is: " + str(weight_in_pounds))
print("Your weight in kilograms is: " + str(weight_in_kg))