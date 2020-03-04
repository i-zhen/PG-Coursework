SELECT Distinct A.artist
FROM Album AS A, Album AS B         /*rename the album to 2 tables*/
WHERE 	A.Type = 'LIVE' 
	AND B.Type = 'COMPILATION' 
	AND A.year = B.year 
	AND A.artist = B.artist
