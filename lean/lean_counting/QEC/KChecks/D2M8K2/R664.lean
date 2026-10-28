import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2656 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2656 = true := by
  decide +kernel

theorem tot2656 : totK PD2M8K2 D2M8K2.t2656 = [0, 0, 0, 341442876939, 505622794793, 53026791500, 0, 0] := by
  decide +kernel

theorem rows2657 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2657 = true := by
  decide +kernel

theorem tot2657 : totK PD2M8K2 D2M8K2.t2657 = [0, 0, 156583173236, 377107394166, 289824757675, 79948583456, 1392055030, 0] := by
  decide +kernel

theorem rows2658 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2658 = true := by
  decide +kernel

theorem tot2658 : totK PD2M8K2 D2M8K2.t2658 = [0, 0, 170935876734, 442277370388, 263567971107, 16513293566, 0, 0] := by
  decide +kernel

theorem rows2659 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2659 = true := by
  decide +kernel

theorem tot2659 : totK PD2M8K2 D2M8K2.t2659 = [0, 0, 91986061513, 428921184164, 347439398285, 36012228663, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
