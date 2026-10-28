import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11312 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11312 = true := by
  decide +kernel

theorem tot11312 : totK PD2M8K2 D2M8K2.t11312 = [0, 148248218101, 421132335117, 323534200434, 38825070655, 0, 0, 0] := by
  decide +kernel

theorem rows11313 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11313 = true := by
  decide +kernel

theorem tot11313 : totK PD2M8K2 D2M8K2.t11313 = [0, 192878384546, 475349307758, 225178574283, 12583874182, 0, 0, 0] := by
  decide +kernel

theorem rows11314 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11314 = true := by
  decide +kernel

theorem tot11314 : totK PD2M8K2 D2M8K2.t11314 = [0, 167886362480, 460927593893, 241666850665, 15530311626, 0, 0, 0] := by
  decide +kernel

theorem rows11315 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11315 = true := by
  decide +kernel

theorem tot11315 : totK PD2M8K2 D2M8K2.t11315 = [0, 182657694199, 471349144079, 254015732496, 19771634861, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
