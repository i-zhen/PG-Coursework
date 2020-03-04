SELECT B.track_title, A.title, A.artist FROM album AS A, tracklist AS B
WHERE 	(A.artist = B.album_artist) 
	AND (A.rating BETWEEN 4 AND 5) AND (A.title = B.album_title)
	AND (B.track_length < '00:02:34') 
	AND (A.year > 1995)
/*this year is 2015, so latest 20 years means year should larger than 1995*/