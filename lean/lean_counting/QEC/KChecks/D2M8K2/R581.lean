import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2324 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2324 = true := by
  decide +kernel

theorem tot2324 : totK PD2M8K2 D2M8K2.t2324 = [0, 0, 197799941409, 463456875254, 238572240371, 21601665459, 0, 0] := by
  decide +kernel

theorem rows2325 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2325 = true := by
  decide +kernel

theorem tot2325 : totK PD2M8K2 D2M8K2.t2325 = [0, 0, 155480716081, 472737693752, 257105904495, 13703961568, 0, 0] := by
  decide +kernel

theorem rows2326 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2326 = true := by
  decide +kernel

theorem tot2326 : totK PD2M8K2 D2M8K2.t2326 = [0, 0, 0, 323034206030, 476465979830, 96944687660, 1557581783, 0] := by
  decide +kernel

theorem rows2327 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2327 = true := by
  decide +kernel

theorem tot2327 : totK PD2M8K2 D2M8K2.t2327 = [0, 0, 161394240974, 446984955627, 277773839416, 34637983810, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
