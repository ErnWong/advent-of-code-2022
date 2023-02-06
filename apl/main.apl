day1 ← ⊃⎕NGET 'day1.txt'1
⎕ ← 'day 1 part 1:', ⌈/+/¨               ⍎¨¨{(0≠≢¨⍵)⊆⍵}  day1
⎕ ← 'day 1 part 2:', +/{⍵[3↑⍒⍵]}+/¨      ⍎¨¨{(0≠≢¨⍵)⊆⍵}  day1

day2 ← ⊃⎕NGET 'day2.example.txt'1
⎕ ← 'day 2 part 1:', +/ {4 + +/ ¯3 0 4 × ⍵ - (⎕A⍳'A X')}¨↓⎕A⍳↑    day2
⍝  
⍝  ⎕←day3←'vJrwpWtwJgWrhcsFMMfFFhFp' 'jqHRNqRjqzjGDLGLrsFMfFZSrLrFZsSL' 'PmmdzqPrVvPwwTWBwg' 'wMqvLMZHhHMvwLHjbvcjnnSBnvTQFn' 'ttgJtRGJQctTZtZT' 'CrZsJsPPZsGzwwsLwLmpwMDw'
⍝  +/((⎕C ⎕A),⎕A)⍳{⊃∪((2÷⍨≢⍵)↑⍵)∩((2÷⍨≢⍵)↓⍵)}¨  ⎕NGET 'day3.txt'
⍝  
⍝  ⎕←day4←'2-4,6-8' '2-3,4-5' '5-7,7-9' '2-8,3-7' '6-6,4-6' '2-6,4-8'
⍝  0≥1↑⍤1⊢{(⍵-4⌽⍵)×((2⌽⍵)-6⌽⍵)}⎕D⍳↑day4
⍝  
⍝  ⎕←day5split←{(0≠≢¨⍵)⊆⍵}day5
⍝  ⎕←day5procedure←{(,/1↑[2]⍵)⌿⍵}⍎¨(0 1 0 1 0 1/⊣/↑↑{(' '≠⍵)⊆⍵}¨⊃day5split[2])
⍝  ⎕←day5initial←' '~⍨¨↓⍉{((⍳2⌷⍴⍵)∊2-⍨4×⍳4÷⍨1+2⌷⍴⍵)/⍵}↑1⊃day5split
⍝  ⎕←day5final←⊃{(⊂1↓⊃⍵[⍺[2]]) @ (⊃⍺[2]) ⊢ (⊂(1↑⊃⍵[⍺[2]]),⊃⍵[⍺[3]]) @ (⊃⍺[3]) ⊢ ⍵}/(↓day5procedure),⊂day5initial
⍝  ⎕←day5answer←⊣/↑day5final
⍝  
⍝  3+1⍳⍨¯1↓1↓{⍵≡∪⍵}⌺4⊢day6
⍝  
⍝  ⎕←day7←'$ cd /' '$ ls' 'dir a' '14848514 b.txt' '8504156 c.dat' 'dir d' '$ cd a' '$ ls' 'dir e' '29116 f' '2557 g' '62596 h.lst' '$ cd e' '$ ls' '584 i' '$ cd ..' '$ cd ..' '$ cd d' '$ ls' '4060174 j' '8033020 d.log' '5626152 d.ext' '7214296 k' 
⍝  ⎕←day7parsed←↑{((2×(1⍴'$') 'cd' '..'≡⍵)-(1⍴'$') 'cd'≡2↑⍵),⊃2⌷⎕VFI⊃1↑⍵}¨{(⍵≠' ')⊆⍵}¨day7
⍝  day7push←{⍵[1] (0,⊃⍵[2])}
⍝  day7pop←{(⍵[1]+{⍵×⍵≤100000}⊃⊃⍵[2]),⊂((1↑⊃⍵[2])+⊃1↓⊃⍵[2])@1⊢1↓⊃⍵[2]}
⍝  day7add←{⍵[1],⊂(⍺[2]+1↑⊃⍵[2])@1⊢⊃⍵[2]}
⍝  ⎕←day7answer←⊃⊃{¯1=⊃⍺:day7push ⍵ ⋄ 1=⊃⍺:day7pop ⍵ ⋄ ⍺ day7add ⍵}⌿(⊂0(1⍴0)),⍨⊖1↓day7parsed
⍝  
⍝  
⍝  ⎕←day8←'30373' '25512' '65332' '33549' '35390'
⍝  +/+/    1,[1]⍨1,⍨1,[1]1,¯1 ¯1↓1 1↓    {(⍵>¯1⌽⌈\⍵)  ∨  (⍵>⌽¯1⌽⌈\⌽⍵)  ∨  (⍵>¯1⊖⌈⍀⍵)  ∨  (⍵>⊖¯1⊖⌈⍀⊖⍵)}    ⍎¨↑day8