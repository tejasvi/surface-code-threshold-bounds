import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7304 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7304 = true := by
  decide +kernel

theorem tot7304 : totK PD2M8K2 D2M8K2.t7304 = [0, 179904433616, 455543387990, 254753180129, 20362501281, 0, 0, 0] := by
  decide +kernel

theorem rows7305 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7305 = true := by
  decide +kernel

theorem tot7305 : totK PD2M8K2 D2M8K2.t7305 = [0, 171529334179, 474628225448, 260220695701, 20406587419, 0, 0, 0] := by
  decide +kernel

theorem rows7306 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7306 = true := by
  decide +kernel

theorem tot7306 : totK PD2M8K2 D2M8K2.t7306 = [0, 0, 175907990003, 446031573319, 257757699605, 25373788367, 0, 0] := by
  decide +kernel

theorem rows7307 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7307 = true := by
  decide +kernel

theorem tot7307 : totK PD2M8K2 D2M8K2.t7307 = [0, 0, 214166911840, 497170947549, 194173297792, 5430665091, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
