import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4208 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4208 = true := by
  decide +kernel

theorem tot4208 : totK PD2M8K2 D2M8K2.t4208 = [0, 0, 0, 309117210852, 504118057644, 91917497083, 0, 0] := by
  decide +kernel

theorem rows4209 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4209 = true := by
  decide +kernel

theorem tot4209 : totK PD2M8K2 D2M8K2.t4209 = [0, 0, 0, 201386825756, 468813654868, 185574388749, 8824320960, 0] := by
  decide +kernel

theorem rows4210 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4210 = true := by
  decide +kernel

theorem tot4210 : totK PD2M8K2 D2M8K2.t4210 = [0, 0, 198340425982, 459025653281, 235191367016, 27951562677, 0, 0] := by
  decide +kernel

theorem rows4211 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4211 = true := by
  decide +kernel

theorem tot4211 : totK PD2M8K2 D2M8K2.t4211 = [0, 0, 180460131308, 460597621346, 233292566196, 16507475844, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
