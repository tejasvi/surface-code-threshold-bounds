import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2672 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2672 = true := by
  decide +kernel

theorem tot2672 : totK PD2M8K2 D2M8K2.t2672 = [0, 0, 210135262142, 473065190815, 183568088606, 11885407614, 0, 0] := by
  decide +kernel

theorem rows2673 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2673 = true := by
  decide +kernel

theorem tot2673 : totK PD2M8K2 D2M8K2.t2673 = [0, 163678763449, 434502473673, 267169779260, 37172107206, 0, 0, 0] := by
  decide +kernel

theorem rows2674 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2674 = true := by
  decide +kernel

theorem tot2674 : totK PD2M8K2 D2M8K2.t2674 = [0, 163506929422, 438859465946, 273934460272, 24475359781, 0, 0, 0] := by
  decide +kernel

theorem rows2675 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2675 = true := by
  decide +kernel

theorem tot2675 : totK PD2M8K2 D2M8K2.t2675 = [0, 80091603534, 355916700137, 366355038296, 72803823925, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
