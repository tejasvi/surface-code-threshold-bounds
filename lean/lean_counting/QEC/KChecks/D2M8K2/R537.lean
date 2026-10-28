import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2148 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2148 = true := by
  decide +kernel

theorem tot2148 : totK PD2M8K2 D2M8K2.t2148 = [0, 177376046481, 463303168657, 243785418490, 15411017147, 0, 0, 0] := by
  decide +kernel

theorem rows2149 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2149 = true := by
  decide +kernel

theorem tot2149 : totK PD2M8K2 D2M8K2.t2149 = [0, 69028294282, 329292234805, 407351739891, 88106141516, 1197396724, 0, 0] := by
  decide +kernel

theorem rows2150 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2150 = true := by
  decide +kernel

theorem tot2150 : totK PD2M8K2 D2M8K2.t2150 = [0, 0, 194877734937, 468496828508, 193636351930, 12040273252, 0, 0] := by
  decide +kernel

theorem rows2151 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2151 = true := by
  decide +kernel

theorem tot2151 : totK PD2M8K2 D2M8K2.t2151 = [0, 160540681199, 438274189626, 281486812439, 39231371375, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
