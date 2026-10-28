import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows432 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t432 = true := by
  decide +kernel

theorem tot432 : totK PA10K2 A10K2.t432 = [0, 110493435566, 863557854982, 2142007622704, 1537432329469, 264734567825, 6904928264, 0, 0, 0] := by
  decide +kernel

theorem rows433 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t433 = true := by
  decide +kernel

theorem tot433 : totK PA10K2 A10K2.t433 = [0, 564362757998, 2005171659226, 2018876620976, 526390406890, 23467532520, 0, 0, 0, 0] := by
  decide +kernel

theorem rows434 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t434 = true := by
  decide +kernel

theorem tot434 : totK PA10K2 A10K2.t434 = [0, 121601852911, 994493299851, 2143750482274, 1510458747895, 244535896160, 6066958478, 0, 0, 0] := by
  decide +kernel

theorem rows435 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t435 = true := by
  decide +kernel

theorem tot435 : totK PA10K2 A10K2.t435 = [0, 0, 488083826551, 1829660194164, 2043797748392, 643665213628, 29031327120, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
