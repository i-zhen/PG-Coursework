SELECT A.artist FROM ALBUM AS A
WHERE EXISTS ( /*EXISTS another year which the gap smaller than 4 years*/
	SELECT B.year FROM ALBUM AS B
	WHERE B.artist = A.artist AND (ABS(A.year-B.year) <= 4)
	AND (A.title != B.title) AND A.type = 'STUDIO' AND B.type ='STUDIO') 
GROUP BY (A.artist) 
HAVING COUNT(A.title) = (SELECT COUNT(TITLE) FROM ALBUM WHERE ARTIST = A.artist)
/*If the group is same to the numbers of the albums of the same artists*/

/*Another Method*/
SELECT A.artist FROM ALBUM AS A, ALBUM AS B
WHERE A.artist = B.artist AND B.type = 'STUDIO' AND A.type = 'STUDIO'
	AND A.year + 4 > B.year AND B.year > A.year AND A.artist NOT IN (
		SELECT C.artist FROM ALBUM AS C, ALBUM AS D
		WHERE C.artist = D.artist AND A.type = 'STUDIO' AND B.type = 'STUDIO'
		AND C.year + 4 < D.year AND C.year > D.year
	)