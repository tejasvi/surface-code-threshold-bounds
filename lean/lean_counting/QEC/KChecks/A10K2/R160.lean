import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows640 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t640 = true := by
  decide +kernel

theorem tot640 : totK PA10K2 A10K2.t640 = [0, 0, 260006046817, 1397175126685, 2238241606421, 918791442382, 69771422414, 0, 0, 0] := by
  decide +kernel

theorem rows641 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t641 = true := by
  decide +kernel

theorem tot641 : totK PA10K2 A10K2.t641 = [0, 0, 0, 516995119158, 1849563028490, 1745954108181, 479061348806, 31082886609, 0, 0] := by
  decide +kernel

theorem rows642 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t642 = true := by
  decide +kernel

theorem tot642 : totK PA10K2 A10K2.t642 = [0, 0, 512068011422, 1733022056782, 1819218294184, 620889789260, 55539373477, 0, 0, 0] := by
  decide +kernel

theorem rows643 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t643 = true := by
  decide +kernel

theorem tot643 : totK PA10K2 A10K2.t643 = [0, 0, 218725902029, 1467560168524, 2165447794848, 777093938493, 46250291535, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
