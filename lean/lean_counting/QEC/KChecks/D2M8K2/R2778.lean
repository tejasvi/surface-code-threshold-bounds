import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11112 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11112 = true := by
  decide +kernel

theorem tot11112 : totK PD2M8K2 D2M8K2.t11112 = [0, 87964691079, 380346626814, 398527660538, 49517970732, 0, 0, 0] := by
  decide +kernel

theorem rows11113 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11113 = true := by
  decide +kernel

theorem tot11113 : totK PD2M8K2 D2M8K2.t11113 = [0, 157749484917, 458814727578, 263163499491, 17402073384, 0, 0, 0] := by
  decide +kernel

theorem rows11114 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11114 = true := by
  decide +kernel

theorem tot11114 : totK PD2M8K2 D2M8K2.t11114 = [0, 168631518356, 452534152920, 240010548127, 12865005954, 0, 0, 0] := by
  decide +kernel

theorem rows11115 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11115 = true := by
  decide +kernel

theorem tot11115 : totK PD2M8K2 D2M8K2.t11115 = [0, 0, 246127978657, 510538370312, 124447436112, 2309606161, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
