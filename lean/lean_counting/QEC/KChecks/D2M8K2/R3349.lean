import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13396 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13396 = true := by
  decide +kernel

theorem tot13396 : totK PD2M8K2 D2M8K2.t13396 = [0, 0, 0, 220745664178, 476038789974, 153287384619, 9521435666, 0] := by
  decide +kernel

theorem rows13397 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13397 = true := by
  decide +kernel

theorem tot13397 : totK PD2M8K2 D2M8K2.t13397 = [0, 0, 87179432255, 359834231980, 337523828373, 80216880718, 3462014130, 0] := by
  decide +kernel

theorem rows13398 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13398 = true := by
  decide +kernel

theorem tot13398 : totK PD2M8K2 D2M8K2.t13398 = [0, 0, 199521616241, 449569637340, 233055572412, 18532771655, 0, 0] := by
  decide +kernel

theorem rows13399 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13399 = true := by
  decide +kernel

theorem tot13399 : totK PD2M8K2 D2M8K2.t13399 = [0, 0, 117941200902, 437477752889, 300605788247, 21002658218, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
