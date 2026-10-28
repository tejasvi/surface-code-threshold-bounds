import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14536 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14536 = true := by
  decide +kernel

theorem tot14536 : totK PD2M8K2 D2M8K2.t14536 = [147472534373, 405893766014, 331014905145, 42790463639, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14537 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14537 = true := by
  decide +kernel

theorem tot14537 : totK PD2M8K2 D2M8K2.t14537 = [189449512601, 471229939825, 230751974066, 15670483300, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14538 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14538 = true := by
  decide +kernel

theorem tot14538 : totK PD2M8K2 D2M8K2.t14538 = [70166284074, 348253466486, 375987156660, 110632549940, 13135967731, 0, 0, 0] := by
  decide +kernel

theorem rows14539 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14539 = true := by
  decide +kernel

theorem tot14539 : totK PD2M8K2 D2M8K2.t14539 = [0, 174804876227, 455044114800, 252787572013, 16244034718, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
