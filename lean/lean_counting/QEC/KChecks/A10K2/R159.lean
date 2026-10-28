import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows636 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t636 = true := by
  decide +kernel

theorem tot636 : totK PA10K2 A10K2.t636 = [0, 299193715415, 1246444097009, 1862369081644, 1129797556892, 214783608041, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows637 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t637 = true := by
  decide +kernel

theorem tot637 : totK PA10K2 A10K2.t637 = [0, 296199512645, 1453470028301, 2231897280892, 1040020590170, 97939646925, 0, 0, 0, 0] := by
  decide +kernel

theorem rows638 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t638 = true := by
  decide +kernel

theorem tot638 : totK PA10K2 A10K2.t638 = [0, 0, 447253752499, 1806969997058, 2136643470366, 693727340411, 42079891856, 0, 0, 0] := by
  decide +kernel

theorem rows639 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t639 = true := by
  decide +kernel

theorem tot639 : totK PA10K2 A10K2.t639 = [0, 0, 551747556442, 1966400157376, 1810743069819, 445779607204, 26479096260, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
