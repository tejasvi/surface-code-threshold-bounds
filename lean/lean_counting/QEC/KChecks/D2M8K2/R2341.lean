import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9364 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9364 = true := by
  decide +kernel

theorem tot9364 : totK PD2M8K2 D2M8K2.t9364 = [0, 159540119492, 418034441226, 268670609826, 60106770377, 2566665356, 0, 0] := by
  decide +kernel

theorem rows9365 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9365 = true := by
  decide +kernel

theorem tot9365 : totK PD2M8K2 D2M8K2.t9365 = [0, 170278346319, 437968856963, 261710521530, 23434910841, 0, 0, 0] := by
  decide +kernel

theorem rows9366 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9366 = true := by
  decide +kernel

theorem tot9366 : totK PD2M8K2 D2M8K2.t9366 = [0, 91681601894, 418563054247, 350972404874, 39489200680, 0, 0, 0] := by
  decide +kernel

theorem rows9367 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9367 = true := by
  decide +kernel

theorem tot9367 : totK PD2M8K2 D2M8K2.t9367 = [0, 0, 301083123654, 515318236664, 91606419089, 1067382613, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
