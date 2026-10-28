import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4180 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4180 = true := by
  decide +kernel

theorem tot4180 : totK PA10K2 A10K2.t4180 = [0, 0, 663491251216, 2027085667875, 1656478039146, 398204049359, 25565504801, 0, 0, 0] := by
  decide +kernel

theorem rows4181 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4181 = true := by
  decide +kernel

theorem tot4181 : totK PA10K2 A10K2.t4181 = [0, 367218047613, 1306018390861, 1883241460066, 1069654547708, 178995699509, 5517381808, 0, 0, 0] := by
  decide +kernel

theorem rows4182 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4182 = true := by
  decide +kernel

theorem tot4182 : totK PA10K2 A10K2.t4182 = [0, 411757640958, 1793689957702, 2018622528954, 578090017397, 32877822373, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4183 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4183 = true := by
  decide +kernel

theorem tot4183 : totK PA10K2 A10K2.t4183 = [0, 0, 710769301963, 2217846063221, 1477933643406, 213007971328, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
