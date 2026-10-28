import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10996 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10996 = true := by
  decide +kernel

theorem tot10996 : totK PD2M8K2 D2M8K2.t10996 = [0, 0, 292731464349, 478572182838, 81342969607, 1206465782, 0, 0] := by
  decide +kernel

theorem rows10997 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10997 = true := by
  decide +kernel

theorem tot10997 : totK PD2M8K2 D2M8K2.t10997 = [0, 177425867739, 450245253974, 270821893996, 29657454275, 0, 0, 0] := by
  decide +kernel

theorem rows10998 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10998 = true := by
  decide +kernel

theorem tot10998 : totK PD2M8K2 D2M8K2.t10998 = [0, 166981478532, 457665061709, 255395131988, 20365309466, 0, 0, 0] := by
  decide +kernel

theorem rows10999 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10999 = true := by
  decide +kernel

theorem tot10999 : totK PD2M8K2 D2M8K2.t10999 = [0, 192354433791, 476410849816, 223923110098, 16104584588, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
