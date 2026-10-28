import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16184 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16184 = true := by
  decide +kernel

theorem tot16184 : totK PD2M8K2 D2M8K2.t16184 = [0, 0, 205400836138, 478101425461, 191486029702, 7855532380, 0, 0] := by
  decide +kernel

theorem rows16185 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16185 = true := by
  decide +kernel

theorem tot16185 : totK PD2M8K2 D2M8K2.t16185 = [0, 0, 0, 315131951725, 467374593149, 76579355840, 1239866073, 0] := by
  decide +kernel

theorem rows16186 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16186 = true := by
  decide +kernel

theorem tot16186 : totK PD2M8K2 D2M8K2.t16186 = [0, 0, 92910888046, 396835209035, 375244110517, 37690825282, 0, 0] := by
  decide +kernel

theorem rows16187 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16187 = true := by
  decide +kernel

theorem tot16187 : totK PD2M8K2 D2M8K2.t16187 = [0, 0, 187557094451, 464779540807, 253590229354, 16727537024, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
