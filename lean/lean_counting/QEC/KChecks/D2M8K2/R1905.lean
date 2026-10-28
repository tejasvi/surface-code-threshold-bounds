import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7620 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7620 = true := by
  decide +kernel

theorem tot7620 : totK PD2M8K2 D2M8K2.t7620 = [0, 107917641086, 436815894107, 339739789754, 40058532717, 0, 0, 0] := by
  decide +kernel

theorem rows7621 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7621 = true := by
  decide +kernel

theorem tot7621 : totK PD2M8K2 D2M8K2.t7621 = [0, 0, 166507375991, 442563923323, 262920965642, 25123945117, 0, 0] := by
  decide +kernel

theorem rows7622 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7622 = true := by
  decide +kernel

theorem tot7622 : totK PD2M8K2 D2M8K2.t7622 = [0, 7564999111, 162394415298, 471551027295, 252178980057, 10884197455, 0, 0] := by
  decide +kernel

theorem rows7623 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7623 = true := by
  decide +kernel

theorem tot7623 : totK PD2M8K2 D2M8K2.t7623 = [0, 179882400115, 458809037326, 247381647934, 23085854419, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
