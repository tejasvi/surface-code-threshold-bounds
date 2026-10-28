import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2216 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2216 = true := by
  decide +kernel

theorem tot2216 : totK PD2M8K2 D2M8K2.t2216 = [0, 187946040774, 447338519350, 228888638061, 45293610530, 2814597007, 0, 0] := by
  decide +kernel

theorem rows2217 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2217 = true := by
  decide +kernel

theorem tot2217 : totK PD2M8K2 D2M8K2.t2217 = [0, 141319590012, 447758559688, 299585044755, 24913154353, 0, 0, 0] := by
  decide +kernel

theorem rows2218 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2218 = true := by
  decide +kernel

theorem tot2218 : totK PD2M8K2 D2M8K2.t2218 = [0, 0, 218159474977, 491216663930, 171535595595, 5011483316, 0, 0] := by
  decide +kernel

theorem rows2219 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2219 = true := by
  decide +kernel

theorem tot2219 : totK PD2M8K2 D2M8K2.t2219 = [0, 0, 201384162677, 477096604278, 201191593051, 10374152040, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
