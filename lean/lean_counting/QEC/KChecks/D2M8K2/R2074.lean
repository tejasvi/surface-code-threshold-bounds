import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8296 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8296 = true := by
  decide +kernel

theorem tot8296 : totK PD2M8K2 D2M8K2.t8296 = [193037702312, 454460350315, 247897011795, 25941040483, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8297 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8297 = true := by
  decide +kernel

theorem tot8297 : totK PD2M8K2 D2M8K2.t8297 = [103656024572, 423235848394, 349123370251, 30473374080, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8298 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8298 = true := by
  decide +kernel

theorem tot8298 : totK PD2M8K2 D2M8K2.t8298 = [0, 210487709637, 490796194350, 179568005607, 4965269624, 0, 0, 0] := by
  decide +kernel

theorem rows8299 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8299 = true := by
  decide +kernel

theorem tot8299 : totK PD2M8K2 D2M8K2.t8299 = [0, 193459596157, 460062840616, 215899455334, 17076867616, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
