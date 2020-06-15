from six.moves import range
import math
from sage.all import *

def multiplication(left,right,ring):

	def _cell_decompose(lst):
		for run_coord in range(len(lst)):
			for thing in lst[run_coord:]:
					yield lst[:run_coord]+[thing]

	def _analysis(M,xaxis,yaxis,zaxis):
		temp = []
		for i in range(xaxis):
			for j in range(yaxis):
				h=0
				if M[h][i][j] > 1:
					for k in range(int(math.log(M[h][i][j],2))):
						# temp += [(k,i,j)] * int( math.log( M[h][i][j], 2 )  * 2**(-k) ) #really?
						temp += [(k,i,j)] * int( M[h][i][j]* 2**(-(k+1)) )
		#remove duplicates
		res = []
		for x in list(_cell_decompose(temp)):
			if x not in res:
				res.append(x)
		return res

	def _decompose(lst, coord = 0):
		if lst[coord] <= 1:
			yield []
		for run_coord in range(coord,len(lst)):
			if lst[run_coord] >= 2:
				temp = [0]*len(lst)
				for i in range(len(lst)):
					temp[i] = lst[i]
				temp[run_coord] -= 2
				temp[run_coord + 1] += 1
				for dec in _decompose(temp,run_coord):
					yield [tuple(temp)] + dec

	def _decomposer(lst):
		possibles = set()
		possibles.add(tuple(lst))
		for dec in _decompose(lst):
			for elem in dec:
				possibles.add(elem) 
		return list(possibles)


	def _create_pair(lst):
		length = 0
		for i in range(len(lst)):
			length += lst[i]*2**i
		length = int(math.log(length,2) + 1)

		pair = [0]*length
		for i in range(length):
			pair[i] = [0]*length
			if i < len(lst):
				pair[0][i] = lst[i]
		return pair



	def _alter_pair(pair,lst,column):
		length = len(lst)
		temp_pair = [0]*length
		for i in range(length):
			temp_pair[i] = [0]*length
			for j in range(length):
				temp_pair[i][j] = pair[i][j]
			temp_pair[i][column] = lst[i]
		for j in range(column + 1,length):
			temp_pair[0][j] += lst[j - column]
		return temp_pair



	def _M_generator(M,column_num  = 0):
		length = len(M)
		if column_num == length - 1:
			yield M
		nth_column = [0]*length
		for i in range(length): 
			nth_column[i] = M[i][column_num]
		#initialized nth column

		for elem in _decomposer(nth_column):
			temp_M = _alter_pair(M,elem,column_num)
			if column_num + 1 < length:
				for MMM in _M_generator(temp_M,column_num + 1):
					yield MMM


	# left = list(left)
	# right = list(right)
	result = {}
	xaxis = len(left) + 1
	yaxis = len(right) + 1
	zaxis = int(math.log(max(max(left),max(right)),2)) + 1
	diags = xaxis + yaxis + zaxis - 3
	
	# bad coefficient choice:
	# m_i are the complex cobordism class of the complex projective space of desired dimension
	# but not these generators 
	# T = TermOrder("wdeglex", (1,2))
	# sage: R = PolynomialRing(QQ, 'x,y', order=T)
	# if diags > len(R.gens()):
	# 	T = TermOrder("wdeglex", [2**x-1 for x in range(1,diags)])
	# 	R = PolynomialRing(Zp(2,prec=3), diags-1, 'm', order=T)
	# 	print('should change ring to', R)
		
	# T = TermOrder("wdeglex", [2**x-1 for x in range(1,diags)])
	# R = PolynomialRing(Zp(2,prec=3), diags-1, 'm', order=T)
	generators = [ring.one()] + list(ring.gens())
	# generators[0] 
	# generators = list(generators)
	generators = tuple(generators)

	
	# generators = self.coefficient_ring().gens
	# initialize matrix
	M = list(range(zaxis))
	for h in range(zaxis):
		M[h] = [0]*xaxis
		for i in range(xaxis):
			M[h][i]=[0]*yaxis
	for j in range(1,yaxis):
		M[0][0][j] = right[j-1]
	for i in range(1,xaxis):
		M[0][i][0] = left[i-1]
		for j in range(1,yaxis):
			M[0][i][j] = 0
	
	Mbackup =deepcopy(M)
	

	cells = _analysis(M,xaxis,yaxis,zaxis)
	found_vary = False
	found_new = True

	while found_new or found_vary:
		n = 1
		coef = 1
		diagonal = [0]*diags
		while n <= diags:
			nth_diagonal = []
			S23 = [0]*zaxis
			for h in range(zaxis):
				for i in range(xaxis):
					for j in range(yaxis):
						S23[h] += M[h][i][j]
				for i in range( max(h, n + 1 - yaxis), min(xaxis + h, n + 1)):
					nth_diagonal.append(M[h][i-h][n-i])
			temp = multinomial(nth_diagonal) 
			if temp != 0:
				coef *= temp    
			diag_sum = 0
			for num in nth_diagonal:
				diag_sum += num
			diagonal[n-1] = diag_sum
			n = n + 1

		for i in range(zaxis):
			coef *= generators[i] ** S23[i]
		i = diags - 1
		while i >= 0 and diagonal[i] == 0:
			i = i - 1
		T_X = tuple(diagonal[:i+1])

		for generated_M in list(_M_generator(_create_pair(T_X))):
			length = len(generated_M)
			W = [0]*length
			Y = [0]*(length - 1)
			for i in range(length):
				W[i] = generated_M[0][i]
			for i in range(length - 1):
				Y[i] = [0]*(length)
				for j in range(length):
					Y[i][j] = generated_M[i+1][j]
			diags = len(generated_M) + len(generated_M[0]) - 2
			diagonal = [0]*diags
			
			n = 1
			coef_2 = coef
			while n < diags:
				S2 = [0]*(length - 1)
				for i in range(length - 1):
					for j in range(length):
						S2[i] += Y[i][j]
				nth_diagonal = [Y[i][n-i-1] for i in range(max(0,n-length), min(n,length-1))]
				B_Y = multinomial(nth_diagonal)
				if B_Y != 0:
					coef_2 *= B_Y    
				diag_sum = 0
				for num in nth_diagonal:
					diag_sum += num
				diagonal[n-1] = diag_sum
				n = n + 1

			i = len(W) - 1
			while i >= 0 and W[i] == 0:
				i = i - 1
			t = tuple(W[:i+1])
			

			for n in range(len(T_X)-1):
				if multinomial([T_X[n+1],diagonal[n]]) != 0 :
					coef_2 *= multinomial([T_X[n+1],diagonal[n]])
			MS = 1
			for i in range(1,length):
				MS *= ((-1)*generators[i ]) ** S2[i-1]

			if t in result:
				result[t] += coef_2 * MS
			else:
				result[t] = coef_2 * MS
	
	# now look for new matrices:
		found_new = False
		found_vary = False

		if len(cells) > 0:        
			for cell in cells: 
				if not found_vary:
					
					for i in range(xaxis):
						for j in range(yaxis):
							for h in range(zaxis):
								M[h][i][j] = Mbackup[h][i][j]
					
					for elem in cell:
						found_vary = False
						h,i,j = elem
						if M[h][i][j] >= 2:
							found_vary = True
							M[h+1][i][j] += 1
							M[h][i][j] -= 2
					if found_vary == True:
						ind = cells.index(cell)
						break
			for k in range(ind,-1,-1):
				cells.pop(k)


		if not found_new and not found_vary :
			# M = Mbackup    
			for h in range(zaxis):
				for i in range(xaxis):
					for j in range(yaxis):
						M[h][i][j] = Mbackup[h][i][j]

		j = 1
		while not found_new and not found_vary and j < yaxis:
			sum = M[0][0][j]
			i = 1
			while not found_new and i < xaxis:
				if sum >= 2**i:
					temp_sum = 0
					for k in range(j):
						temp_sum += M[0][i][k]
					if temp_sum != 0:
						found_new = True
						
						#trouble ahead
						for q in range(1,j):
							M[0][0][q] = right[q - 1]
							for s in range(1,xaxis):
								M[0][s][0] = M[0][s][0] + M[0][s][q]
								M[0][s][q] = 0
						for s in range(1,i):
							M[0][s][0] = M[0][s][0] + M[0][s][j]
							M[0][s][j] = 0
						#was trouble

						M[0][i][0] = M[0][i][0] - 1
						M[0][i][j] = M[0][i][j] + 1
						M[0][0][j] = sum - 2**i
						cells = _analysis(M,xaxis,yaxis,zaxis)
						for h in range(zaxis):
							for i in range(xaxis):
								for j in range(yaxis):
									Mbackup[h][i][j] = M[h][i][j]
					else:
						sum = sum + M[0][i][j] * 2**i
				else:
					sum = sum + M[0][i][j] * 2**i
				i = i + 1
			j = j + 1
	return result

def multinomial(list):
	res, i = 1, 1
	for a in list:
		if a != 0: 
			for j in range(1,a+1):
				res *= i
				res //= j
				i += 1
		else:
			continue
	if i == 1:
		res = 0
	return res



