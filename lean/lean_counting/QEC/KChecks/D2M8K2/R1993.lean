import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7972 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7972 = true := by
  decide +kernel

theorem tot7972 : totK PD2M8K2 D2M8K2.t7972 = [0, 0, 106105830409, 441824686737, 343236050374, 33697557093, 0, 0] := by
  decide +kernel

theorem rows7973 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7973 = true := by
  decide +kernel

theorem tot7973 : totK PD2M8K2 D2M8K2.t7973 = [0, 0, 0, 221920932050, 473911331530, 209158156441, 13908735795, 0] := by
  decide +kernel

theorem rows7974 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7974 = true := by
  decide +kernel

theorem tot7974 : totK PD2M8K2 D2M8K2.t7974 = [0, 0, 131647229527, 379107302343, 330084290327, 79740272662, 1409560813, 0] := by
  decide +kernel

theorem rows7975 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7975 = true := by
  decide +kernel

theorem tot7975 : totK PD2M8K2 D2M8K2.t7975 = [0, 0, 170256054884, 439470557354, 278499458236, 27401184143, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
