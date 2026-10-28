import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3228 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3228 = true := by
  decide +kernel

theorem tot3228 : totK PA10K2 A10K2.t3228 = [0, 0, 0, 493786018842, 1919266506042, 2063276351251, 483307418937, 12926121504, 0, 0] := by
  decide +kernel

theorem rows3229 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3229 = true := by
  decide +kernel

theorem tot3229 : totK PA10K2 A10K2.t3229 = [0, 0, 0, 575897542181, 1800536646701, 1760304513717, 612087949282, 54615487832, 0, 0] := by
  decide +kernel

theorem rows3230 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3230 = true := by
  decide +kernel

theorem tot3230 : totK PA10K2 A10K2.t3230 = [0, 0, 0, 286168622330, 1558747384746, 2178026786894, 760069123974, 56295361699, 0, 0] := by
  decide +kernel

theorem rows3231 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3231 = true := by
  decide +kernel

theorem tot3231 : totK PA10K2 A10K2.t3231 = [0, 0, 0, 0, 527870746900, 1794139805550, 1759994799108, 481847881086, 31018567651, 0] := by
  decide +kernel

end QECKChecks.A10K2
