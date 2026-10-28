import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7876 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7876 = true := by
  decide +kernel

theorem tot7876 : totK PA10K2 A10K2.t7876 = [0, 0, 0, 672104697884, 2239623002284, 1867030064100, 336764000306, 6962742351, 0, 0] := by
  decide +kernel

theorem rows7877 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7877 = true := by
  decide +kernel

theorem tot7877 : totK PA10K2 A10K2.t7877 = [0, 0, 0, 626859995391, 1971569977731, 1816404029000, 518923229018, 34099770725, 0, 0] := by
  decide +kernel

theorem rows7878 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7878 = true := by
  decide +kernel

theorem tot7878 : totK PA10K2 A10K2.t7878 = [0, 0, 0, 462181334973, 1743291238774, 1904810132196, 535230215542, 32523532663, 0, 0] := by
  decide +kernel

theorem rows7879 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7879 = true := by
  decide +kernel

theorem tot7879 : totK PA10K2 A10K2.t7879 = [0, 0, 0, 44601108633, 880709042113, 2058622182690, 1452655453328, 323617181086, 13576218110, 0] := by
  decide +kernel

end QECKChecks.A10K2
