import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8016 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8016 = true := by
  decide +kernel

theorem tot8016 : totK PA10K2 A10K2.t8016 = [0, 0, 0, 352922458129, 1586279803877, 2086975105254, 824924039420, 67703147453, 0, 0] := by
  decide +kernel

theorem rows8017 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8017 = true := by
  decide +kernel

theorem tot8017 : totK PA10K2 A10K2.t8017 = [0, 0, 0, 485869787686, 1851505641130, 2030354374601, 589052896997, 18729111255, 0, 0] := by
  decide +kernel

theorem rows8018 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8018 = true := by
  decide +kernel

theorem tot8018 : totK PA10K2 A10K2.t8018 = [0, 0, 0, 0, 788503102830, 2257088862900, 1555735387393, 249558282642, 6904928264, 0] := by
  decide +kernel

theorem rows8019 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8019 = true := by
  decide +kernel

theorem tot8019 : totK PA10K2 A10K2.t8019 = [0, 0, 0, 589830162524, 1936414133607, 1887799384579, 595804500204, 51421223111, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
