import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t16 = true := by
  decide +kernel

theorem tot16 : totK PA10K2 A10K2.t16 = [467330755411, 1874847432131, 1964569701018, 473893672620, 25686058060, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows17 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t17 = true := by
  decide +kernel

theorem tot17 : totK PA10K2 A10K2.t17 = [218412668081, 1108585727192, 2058379024413, 1340765185573, 275515635872, 20070762815, 0, 0, 0, 0] := by
  decide +kernel

theorem rows18 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t18 = true := by
  decide +kernel

theorem tot18 : totK PA10K2 A10K2.t18 = [167590323971, 840031236741, 1863228875321, 1572938793937, 323262389030, 10760911071, 0, 0, 0, 0] := by
  decide +kernel

theorem rows19 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t19 = true := by
  decide +kernel

theorem tot19 : totK PA10K2 A10K2.t19 = [257551339912, 1354775736889, 1949900858676, 869691696519, 132847108747, 15171143123, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
