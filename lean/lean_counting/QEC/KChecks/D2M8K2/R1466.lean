import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5864 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5864 = true := by
  decide +kernel

theorem tot5864 : totK PD2M8K2 D2M8K2.t5864 = [156043322821, 443716291304, 284859471931, 27793411699, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5865 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5865 = true := by
  decide +kernel

theorem tot5865 : totK PD2M8K2 D2M8K2.t5865 = [177506813398, 470599179945, 234875102916, 13245483224, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5866 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5866 = true := by
  decide +kernel

theorem tot5866 : totK PD2M8K2 D2M8K2.t5866 = [0, 284987450398, 508439398499, 105162623850, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows5867 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5867 = true := by
  decide +kernel

theorem tot5867 : totK PD2M8K2 D2M8K2.t5867 = [104907210977, 338080008587, 348927350867, 96543216733, 3884009855, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
