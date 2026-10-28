import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4688 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4688 = true := by
  decide +kernel

theorem tot4688 : totK PD2M8K2 D2M8K2.t4688 = [0, 0, 232064857174, 484026527624, 166398290908, 9473607896, 0, 0] := by
  decide +kernel

theorem rows4689 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4689 = true := by
  decide +kernel

theorem tot4689 : totK PD2M8K2 D2M8K2.t4689 = [0, 154825709772, 404448769130, 276647985256, 62972990673, 2566665356, 0, 0] := by
  decide +kernel

theorem rows4690 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4690 = true := by
  decide +kernel

theorem tot4690 : totK PD2M8K2 D2M8K2.t4690 = [0, 166090603985, 438940774968, 277553312760, 30498735743, 0, 0, 0] := by
  decide +kernel

theorem rows4691 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4691 = true := by
  decide +kernel

theorem tot4691 : totK PD2M8K2 D2M8K2.t4691 = [0, 90952881055, 384436529915, 351268184763, 57579366509, 1096156699, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
