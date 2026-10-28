import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7520 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7520 = true := by
  decide +kernel

theorem tot7520 : totK PD2M8K2 D2M8K2.t7520 = [0, 178891048405, 446253454496, 253140068455, 21660674231, 0, 0, 0] := by
  decide +kernel

theorem rows7521 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7521 = true := by
  decide +kernel

theorem tot7521 : totK PD2M8K2 D2M8K2.t7521 = [0, 74527797021, 366298924272, 383313627124, 70936651859, 1096156699, 0, 0] := by
  decide +kernel

theorem rows7522 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7522 = true := by
  decide +kernel

theorem tot7522 : totK PD2M8K2 D2M8K2.t7522 = [0, 3736707029, 262631541598, 502092291959, 125548052717, 3880716147, 0, 0] := by
  decide +kernel

theorem rows7523 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7523 = true := by
  decide +kernel

theorem tot7523 : totK PD2M8K2 D2M8K2.t7523 = [0, 193457362611, 464081749123, 246125835479, 23350948179, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
