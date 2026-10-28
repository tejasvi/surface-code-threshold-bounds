import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2364 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2364 = true := by
  decide +kernel

theorem tot2364 : totK PD2M8K2 D2M8K2.t2364 = [0, 133073311742, 340881654569, 281366168365, 137084390308, 13566920432, 0, 0] := by
  decide +kernel

theorem rows2365 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2365 = true := by
  decide +kernel

theorem tot2365 : totK PD2M8K2 D2M8K2.t2365 = [0, 190399186423, 457053646361, 226755859801, 17085825678, 0, 0, 0] := by
  decide +kernel

theorem rows2366 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2366 = true := by
  decide +kernel

theorem tot2366 : totK PD2M8K2 D2M8K2.t2366 = [0, 87093597246, 386371336057, 360243611924, 51996394290, 1369150432, 0, 0] := by
  decide +kernel

theorem rows2367 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2367 = true := by
  decide +kernel

theorem tot2367 : totK PD2M8K2 D2M8K2.t2367 = [0, 0, 294394553075, 508684106198, 92498701390, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
