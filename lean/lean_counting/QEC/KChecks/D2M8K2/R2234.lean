import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8936 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8936 = true := by
  decide +kernel

theorem tot8936 : totK PD2M8K2 D2M8K2.t8936 = [0, 0, 261315955881, 489377660106, 128235168594, 2318623666, 0, 0] := by
  decide +kernel

theorem rows8937 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8937 = true := by
  decide +kernel

theorem tot8937 : totK PD2M8K2 D2M8K2.t8937 = [0, 55368390034, 251849166232, 388685035673, 150710973510, 10786826731, 0, 0] := by
  decide +kernel

theorem rows8938 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8938 = true := by
  decide +kernel

theorem tot8938 : totK PD2M8K2 D2M8K2.t8938 = [0, 179048609488, 476137102641, 226990854137, 12084350913, 0, 0, 0] := by
  decide +kernel

theorem rows8939 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8939 = true := by
  decide +kernel

theorem tot8939 : totK PD2M8K2 D2M8K2.t8939 = [0, 179792741300, 481183449483, 229454028174, 12163338161, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
