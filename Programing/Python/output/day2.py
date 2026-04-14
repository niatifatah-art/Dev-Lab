#This is day 2 of learning Python. Today, I will.
#16/03/2026

#lesson 4
# In Python, you can use the type() function to check the data type of a variable. This can be useful for debugging and understanding how your program works.
#learning about type conversion
birth_year = int(input("Birth year: "))
age = 2026 - int(birth_year)
print("Your age is: " + str(age))

print(type(age))
print(type(birth_year))

#exercise 4
# Create a program that asks the user for their height in centimeters and converts it to inches.
height_in_cm = float(input("What is your height in centimeters? "))
height_in_inches = height_in_cm / 2.54
print("Your height in centimeters is: " + str(height_in_cm))
print("Your height in inches is: " + str(height_in_inches))

#lesson 5
# In Python, you can use either single quotes (' ') or double quotes (" ") to define
# a string. This allows you to include quotes within your string without needing to escape them.
# For example, if you want to include a single quote in your string, you can use double quotes to define the string:
subject = "Fatah's favorite subject is Algebra programming."
print(subject)

color = 'The color of the sky is "blue"'
print(color)

'''
Hi Fatah,
you're officially a worker in Google. Congratulations on your new job! I wish you all the best in your career and hope you enjoy working there.
Best regards,
'''

