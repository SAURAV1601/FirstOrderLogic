# First Order Logic Engine

# Description
A pharmacy is developing a self-service automated system to alert customers about
potential drug interactions for both prescription and over-the-counter drugs. Many medications
should not be taken together or should not be taken if a patient has certain symptoms and
allergies. Evaluating all the criteria for whether a patient can take a particular medication requires
the patient's medical history and expert knowledge from a health care provider. The system,
however, can provide an instant guideline to keep patients informed and minimize the risks. Patient history and drug compatibility data will be encoded as first order logic clauses
in the knowledge base. The program takes a query of new drug list and provide a logical
conclusion whether to issue a warning.

# Input format
N = NUMBER OF QUERIES <br>
QUERY 1 <br>
... <br>
QUERY N <br>
K = NUMBER OF GIVEN SENTENCES IN THE KNOWLEDGE BASE<br>
SENTENCE 1 <br>
... <br>
SENTENCE K <br>

# Output format
For each query, determine if that query can be inferred from the knowledge base or not, one
query per line:<br>
ANSWER 1 <br> 
... <br>
ANSWER N <br>
