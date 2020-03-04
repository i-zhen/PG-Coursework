SELECT AVG(A.track_length) FROM tracklist AS A, album AS B
WHERE 	(B.title = A.album_title) 		/*Select the album*/
	AND (Year Between 1990 AND 1999) 	/*90s*/
	AND B.title IN (SELECT C.album_title FROM tracklist AS C
			GROUP BY (C.album_title)
			HAVING COUNT(C.track_title) >= 10)
			/*at least 10 songs*/