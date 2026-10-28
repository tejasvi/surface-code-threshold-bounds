import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1412 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1412 = true := by
  decide +kernel

theorem tot1412 : totK PA10K2 A10K2.t1412 = [0, 0, 0, 0, 747305081718, 2082675620640, 1603072659194, 384083917238, 25371180993, 0] := by
  decide +kernel

theorem rows1413 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1413 = true := by
  decide +kernel

theorem tot1413 : totK PA10K2 A10K2.t1413 = [0, 0, 0, 297214783146, 1173312194600, 1838032742421, 1098685273658, 185984058390, 5460492893, 0] := by
  decide +kernel

theorem rows1414 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1414 = true := by
  decide +kernel

theorem tot1414 : totK PA10K2 A10K2.t1414 = [0, 0, 0, 183226931894, 1150294890294, 2004678333966, 964033464474, 125993648357, 5656154743, 0] := by
  decide +kernel

theorem rows1415 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1415 = true := by
  decide +kernel

theorem tot1415 : totK PA10K2 A10K2.t1415 = [0, 0, 0, 446736409901, 1650195328101, 1838954077371, 529737927173, 37026429097, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
