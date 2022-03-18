
<!-- PROJECT LOGO -->
<br />
<p align="center">
  <h3 align="center">AFD & AFN Project</h3>

  <p align="center">
The project consists of the implementation of the basic algorithms of finite automata and regular expressions. Generally speaking, the program will accept as input a regular expression **r** and a string **w**. From the regular expression **r** an AFN will be built, which will then be transformed into an AFD. On the other hand, also using the same regular expression **r** will generate an AFD directly. With these automata it will be determined if the string **w** belongs to **L(r)** or not.
    <br />
  </p>
</p>

<!-- TABLE OF CONTENTS -->
<details open="open">
  <summary>Table of Contents</summary>
  <ol>
    <li>
      <a href="#about-the-project">About The Project</a>
      <ul>
        <li><a href="#implemented-functionalities">Implemented functionalities</a></li>
        <li><a href="#built-with">Built With</a></li>
      </ul>
    </li>
    <li>
      <a href="#getting-started">Getting Started</a>
      <ul>
        <li><a href="#prerequisites">Prerequisites</a></li>
        <li><a href="#installation">Installation</a></li>
      </ul>
    </li>
    <li><a href="#license">License</a></li>
  </ol>
</details>



<!-- ABOUT THE PROJECT -->
## About The Project


In NodeJS a library is implemented that will allow the program to be run through the WEB thanks to Browserify and the implementation of MakeFile. You will be able to enter different expressions that will allow the user to know your automaton depending on the method you choose.

The system is divided into three phases:

1. Implementation of the Thompson algorithm to be able to transform an NFA and implement the subset algorithm to be able to build its DFA

2. Implement the direct construction algorithm to build a DFA from a regular expression.

3. Perform a simulation for the three algorithms

The program is built with a simple interface to better understand what is being worked on and uses the https://graphviz.org/ library to be able to paint the automata. 


The objectives of the project are:

  * Implementation of the basic algorithms of finite automata and regular expressions and have the basis for the implementation of the lexical analyzer generator.
 
### Implemented functionalities

  * Implementation of the Thompson Construction algorithm.
  * Implementation of the Subset Construction algorithm.
  * Implementation of the AFD Construction algorithm given a regular expression r.
  * Implementation of simulation of an AFN.
  * Implementation of simulation of an AFD.


### Built With

This section should list any major frameworks that you built your project using. 
* [Node JS](https://nodejs.org/en/)
* [Graphviz](https://graphviz.org/)
* [MakeFile](https://makefiletutorial.com/)

<!-- GETTING STARTED -->
## Getting Started

To get a local copy up and running follow these simple example steps.

### Prerequisites

To be able to use this client locally. You must have the following dependencies installed on your computer

* npm
  ```sh
  npm install npm@latest -g
  ```
* 200 OK! Web Server 
 ```
 This is not necessary but it can make everythin easier
  ```

### Installation

1. Clone the repo
   ```sh
   git clone 
   ```
2. Install NPM packages
   * Move to the folder project 
   ```sh
   npm i
   ```
3. Install 200 OK! WebServer   
  * Move to google and install this application: [200 OK!](https://chrome.google.com/webstore/detail/web-server-for-chrome/ofhbbkphhbklhfoeikjpcbhemlocgigb?hl=en)
 

## Run the program 

Move the public folder to the web server and enjoy the program

<!-- LICENSE -->
## License

- https://github.com/mretolaza/proyecto1-automatas/blob/main/LICENSE


<!-- CONTACT -->
## Contact

María Mercedes Retolaza Reyna - - ret16339@uvg.edu.gt

Project Link: [https://github.com/mretolaza/proyecto1-automatas](https://github.com/mretolaza/proyecto1-automatas)
