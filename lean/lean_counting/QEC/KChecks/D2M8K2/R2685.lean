import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10740 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10740 = true := by
  decide +kernel

theorem tot10740 : totK PD2M8K2 D2M8K2.t10740 = [0, 0, 92231159909, 383496383280, 391649566677, 40218657886, 0, 0] := by
  decide +kernel

theorem rows10741 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10741 = true := by
  decide +kernel

theorem tot10741 : totK PD2M8K2 D2M8K2.t10741 = [0, 0, 169308436682, 434450341897, 266891814233, 24688966409, 0, 0] := by
  decide +kernel

theorem rows10742 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10742 = true := by
  decide +kernel

theorem tot10742 : totK PD2M8K2 D2M8K2.t10742 = [0, 0, 156503919853, 467726996506, 275907179707, 22756149130, 0, 0] := by
  decide +kernel

theorem rows10743 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10743 = true := by
  decide +kernel

theorem tot10743 : totK PD2M8K2 D2M8K2.t10743 = [0, 0, 0, 222009153074, 478666255755, 179918565852, 12570117775, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
