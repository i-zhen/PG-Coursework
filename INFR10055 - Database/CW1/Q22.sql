SELECT A.artist FROM Album AS A
WHERE A.artist IN                         /*Select the artists who have studio album*/
	(SELECT B.artist FROM Album AS B  /*Select the artists who only have studio album*/
	WHERE B.Type IN ('STUDIO')) 
GROUP BY A.artist 		          /*Group them, elimate the same name of artists*/
HAVING COUNT (DISTINCT A.Type)  = 1       /*because artist have studio album, if distict type is 1, thus we find the answer*/
