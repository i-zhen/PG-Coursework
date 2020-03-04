CREATE TYPE ENUMTYPE_artist AS ENUM ('PERSON', 'BAND');
CREATE TABLE Artist 
(
	Name varchar(255) NOT NULL,
	Type ENUMTYPE_artist NOT NULL,
	Country varchar(255) NOT NULL,
	PRIMARY KEY (Name)
);
