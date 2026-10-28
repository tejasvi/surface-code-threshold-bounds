import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5276 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5276 = true := by
  decide +kernel

theorem tot5276 : totK PD2M8K2 D2M8K2.t5276 = [0, 86551020347, 356354627170, 368269878011, 70887316349, 1369150432, 0, 0] := by
  decide +kernel

theorem rows5277 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5277 = true := by
  decide +kernel

theorem tot5277 : totK PD2M8K2 D2M8K2.t5277 = [0, 26907745683, 322743753364, 493954239130, 70383718274, 0, 0, 0] := by
  decide +kernel

theorem rows5278 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5278 = true := by
  decide +kernel

theorem tot5278 : totK PD2M8K2 D2M8K2.t5278 = [0, 174400595209, 440537874057, 277367606949, 30455970377, 0, 0, 0] := by
  decide +kernel

theorem rows5279 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5279 = true := by
  decide +kernel

theorem tot5279 : totK PD2M8K2 D2M8K2.t5279 = [0, 215214106330, 494366386825, 203455880654, 8927609045, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
