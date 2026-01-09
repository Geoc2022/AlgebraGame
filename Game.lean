import Game.Levels.Monoid
import Game.Levels.Group
import Game.Levels.PowMonoid
import Game.Levels.PowGroup
import Game.Levels.GroupHom
import Game.Levels.Ring
import Game.Levels.GroupExamples


-- Here's what we'll put on the title screen
Title "Algebra Game"
Introduction
"
# Welcome to the Algebra Game
#### An introduction to algebraic structures.

In this game, we will build the basic theory of Groups, Rings, and Fields from scratch. We'll do this by solving levels of a computer puzzle game called Lean.

It's recommend that you play the [Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/NNG4) to learn the basics of Lean before playing this game.
"

Info "
Uses Lean4.40
"

/-! Information to be displayed on the servers landing page. -/
Languages "English"
CaptionShort "Introduction to basic algebra"
CaptionLong "In this game you will learn the basics of algebra"
-- Prerequisites "" -- add this if your game depends on other games
-- CoverImage "images/cover.png"

/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame
