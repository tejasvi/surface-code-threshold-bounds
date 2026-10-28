import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7076 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7076 = true := by
  decide +kernel

theorem tot7076 : totK PA10K2 A10K2.t7076 = [0, 0, 308540766384, 1516816807208, 2195932942049, 945656535911, 69408051852, 0, 0, 0] := by
  decide +kernel

theorem rows7077 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7077 = true := by
  decide +kernel

theorem tot7077 : totK PA10K2 A10K2.t7077 = [0, 0, 145264893317, 765362090592, 1869515188473, 1698830772819, 333173995169, 11918539728, 0, 0] := by
  decide +kernel

theorem rows7078 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7078 = true := by
  decide +kernel

theorem tot7078 : totK PA10K2 A10K2.t7078 = [0, 0, 454380585709, 1787091994853, 2030835479947, 623088164568, 33055448423, 0, 0, 0] := by
  decide +kernel

theorem rows7079 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7079 = true := by
  decide +kernel

theorem tot7079 : totK PA10K2 A10K2.t7079 = [0, 0, 291242389419, 1442198060208, 2180832502360, 1029580988706, 87013900920, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
