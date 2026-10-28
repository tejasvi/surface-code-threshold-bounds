import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14024 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14024 = true := by
  decide +kernel

theorem tot14024 : totK PD2M8K2 D2M8K2.t14024 = [0, 0, 197838017569, 427991216212, 230113290190, 37974411632, 1225787871, 0] := by
  decide +kernel

theorem rows14025 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14025 = true := by
  decide +kernel

theorem tot14025 : totK PD2M8K2 D2M8K2.t14025 = [0, 0, 216951183492, 492966365458, 196907229294, 6921706829, 0, 0] := by
  decide +kernel

theorem rows14026 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14026 = true := by
  decide +kernel

theorem tot14026 : totK PD2M8K2 D2M8K2.t14026 = [0, 173499625219, 376939041445, 217106804351, 114629379573, 11742091552, 0, 0] := by
  decide +kernel

theorem rows14027 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14027 = true := by
  decide +kernel

theorem tot14027 : totK PD2M8K2 D2M8K2.t14027 = [0, 152040693895, 458032493681, 265745126550, 20184520368, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
