import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4012 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4012 = true := by
  decide +kernel

theorem tot4012 : totK PA10K2 A10K2.t4012 = [0, 481051651601, 1789800968725, 1925068738691, 678884304980, 65283187088, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4013 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4013 = true := by
  decide +kernel

theorem tot4013 : totK PA10K2 A10K2.t4013 = [0, 214899311104, 1135678986629, 2119066542835, 1223273830097, 186503426680, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows4014 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4014 = true := by
  decide +kernel

theorem tot4014 : totK PA10K2 A10K2.t4014 = [0, 568992563035, 1903583789478, 1909036249620, 567210641862, 41862154265, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4015 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4015 = true := by
  decide +kernel

theorem tot4015 : totK PA10K2 A10K2.t4015 = [0, 31680252160, 912311249145, 2274161791900, 1602804994811, 287158048622, 6851704726, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
