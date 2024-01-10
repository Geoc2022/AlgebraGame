import Game.Levels.DemoWorld

-- Here's what we'll put on the title screen
Title "Algebra Game"
Introduction
"
# Welcome to the Algebra Game
"

Info "
Uses Lean4.40
"

/-! Information to be displayed on the servers landing page. -/
Languages "English"
CaptionShort "Introduction to basic algebra"
CaptionLong "In this game you will learn the basics of algebra based on the \"An Intergrated Approch to Abstact Algebra\" by Joesph Silverman"
-- Prerequisites "" -- add this if your game depends on other games
-- CoverImage "images/cover.png"

/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame
