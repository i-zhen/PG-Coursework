SELECT A.album_title, SUM(A.track_length) FROM TRACKLIST AS A
WHERE (SELECT MAX(track_no) FROM tracklist WHERE album_title = A.album_title) =
	(SELECT COUNT(track_no) FROM tracklist WHERE album_title = A.album_title) 
	/*Check if there are no tracks missing*/
GROUP BY (A.album_title)