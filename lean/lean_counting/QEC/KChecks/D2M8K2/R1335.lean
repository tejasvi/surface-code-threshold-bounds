import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5340 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5340 = true := by
  decide +kernel

theorem tot5340 : totK PD2M8K2 D2M8K2.t5340 = [0, 0, 0, 334489653741, 496912999610, 60016656911, 0, 0] := by
  decide +kernel

theorem rows5341 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5341 = true := by
  decide +kernel

theorem tot5341 : totK PD2M8K2 D2M8K2.t5341 = [0, 0, 171485742426, 420017552903, 246257863792, 48796323957, 1376099875, 0] := by
  decide +kernel

theorem rows5342 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5342 = true := by
  decide +kernel

theorem tot5342 : totK PD2M8K2 D2M8K2.t5342 = [0, 0, 186199981967, 459932134012, 243793216886, 17785730483, 0, 0] := by
  decide +kernel

theorem rows5343 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5343 = true := by
  decide +kernel

theorem tot5343 : totK PD2M8K2 D2M8K2.t5343 = [0, 121950136720, 334779162807, 293640704097, 143102028444, 13566916688, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
