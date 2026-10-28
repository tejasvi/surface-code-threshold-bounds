import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11368 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11368 = true := by
  decide +kernel

theorem tot11368 : totK PD2M8K2 D2M8K2.t11368 = [189007297548, 477197030721, 223258036186, 12442068664, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11369 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11369 = true := by
  decide +kernel

theorem tot11369 : totK PD2M8K2 D2M8K2.t11369 = [0, 290263693863, 500828504676, 112232630983, 1198073392, 0, 0, 0] := by
  decide +kernel

theorem rows11370 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11370 = true := by
  decide +kernel

theorem tot11370 : totK PD2M8K2 D2M8K2.t11370 = [28838223975, 209761119861, 445327654314, 187566075012, 12010829577, 0, 0, 0] := by
  decide +kernel

theorem rows11371 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11371 = true := by
  decide +kernel

theorem tot11371 : totK PD2M8K2 D2M8K2.t11371 = [187685661279, 466064621950, 251652689476, 23134859598, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
