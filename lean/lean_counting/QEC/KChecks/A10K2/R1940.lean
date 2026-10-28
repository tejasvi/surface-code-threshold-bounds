import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7760 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7760 = true := by
  decide +kernel

theorem tot7760 : totK PA10K2 A10K2.t7760 = [0, 0, 0, 122511336145, 1084716451073, 2152287858779, 1356588560535, 210609485041, 6066958478, 0] := by
  decide +kernel

theorem rows7761 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7761 = true := by
  decide +kernel

theorem tot7761 : totK PA10K2 A10K2.t7761 = [0, 0, 0, 0, 604864684323, 2043839298779, 1902574405498, 420642301142, 11910457242, 0] := by
  decide +kernel

theorem rows7762 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7762 = true := by
  decide +kernel

theorem tot7762 : totK PA10K2 A10K2.t7762 = [0, 460408347756, 1506315802292, 1444951545558, 392474579953, 203883421702, 512267636541, 336461662055, 43132710386, 0] := by
  decide +kernel

theorem rows7763 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7763 = true := by
  decide +kernel

theorem tot7763 : totK PA10K2 A10K2.t7763 = [0, 386575793294, 1637199324110, 2001177590395, 721056902556, 55925584929, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
