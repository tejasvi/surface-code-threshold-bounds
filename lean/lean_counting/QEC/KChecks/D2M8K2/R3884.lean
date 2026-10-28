import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15536 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15536 = true := by
  decide +kernel

theorem tot15536 : totK PD2M8K2 D2M8K2.t15536 = [0, 89058976036, 388613266115, 360572996473, 76533885599, 10444649207, 0, 0] := by
  decide +kernel

theorem rows15537 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15537 = true := by
  decide +kernel

theorem tot15537 : totK PD2M8K2 D2M8K2.t15537 = [0, 0, 172553702278, 465930719017, 253407602374, 14929139160, 0, 0] := by
  decide +kernel

theorem rows15538 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15538 = true := by
  decide +kernel

theorem tot15538 : totK PD2M8K2 D2M8K2.t15538 = [0, 0, 174277883158, 472883405431, 233418323470, 8936256697, 0, 0] := by
  decide +kernel

theorem rows15539 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15539 = true := by
  decide +kernel

theorem tot15539 : totK PD2M8K2 D2M8K2.t15539 = [0, 197141082129, 459877159081, 241431424580, 27247453526, 2174602308, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
