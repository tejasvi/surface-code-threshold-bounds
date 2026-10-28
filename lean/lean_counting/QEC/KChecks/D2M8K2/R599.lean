import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2396 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2396 = true := by
  decide +kernel

theorem tot2396 : totK PD2M8K2 D2M8K2.t2396 = [0, 0, 168562559602, 451171236049, 264948525986, 19535652385, 0, 0] := by
  decide +kernel

theorem rows2397 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2397 = true := by
  decide +kernel

theorem tot2397 : totK PD2M8K2 D2M8K2.t2397 = [0, 90585905067, 251139100139, 339907588760, 215426767707, 19127502544, 0, 0] := by
  decide +kernel

theorem rows2398 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2398 = true := by
  decide +kernel

theorem tot2398 : totK PD2M8K2 D2M8K2.t2398 = [0, 171733351067, 478549097890, 234623858185, 11005665056, 0, 0, 0] := by
  decide +kernel

theorem rows2399 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2399 = true := by
  decide +kernel

theorem tot2399 : totK PD2M8K2 D2M8K2.t2399 = [0, 155946893093, 442942418285, 269183056418, 24970623466, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
