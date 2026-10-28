import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5320 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5320 = true := by
  decide +kernel

theorem tot5320 : totK PA10K2 A10K2.t5320 = [0, 0, 517272046629, 1822102469081, 1828775406764, 489652173363, 30831673886, 0, 0, 0] := by
  decide +kernel

theorem rows5321 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5321 = true := by
  decide +kernel

theorem tot5321 : totK PA10K2 A10K2.t5321 = [0, 520278790885, 1700186626373, 1871306200862, 738453593397, 70193027768, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5322 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5322 = true := by
  decide +kernel

theorem tot5322 : totK PA10K2 A10K2.t5322 = [0, 39428607255, 1007023703712, 2312294158286, 1242025436138, 113177740052, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5323 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5323 = true := by
  decide +kernel

theorem tot5323 : totK PA10K2 A10K2.t5323 = [0, 486355993374, 1756815755206, 1894285158616, 720374240405, 122338501038, 6354482628, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
