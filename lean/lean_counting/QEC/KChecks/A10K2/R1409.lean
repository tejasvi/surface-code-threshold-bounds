import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5636 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5636 = true := by
  decide +kernel

theorem tot5636 : totK PA10K2 A10K2.t5636 = [0, 471073901270, 1697381856892, 1903388053287, 653778112238, 52217710783, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5637 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5637 = true := by
  decide +kernel

theorem tot5637 : totK PA10K2 A10K2.t5637 = [0, 95577804451, 1203515517963, 2290536431482, 1043850670792, 86815038553, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5638 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5638 = true := by
  decide +kernel

theorem tot5638 : totK PA10K2 A10K2.t5638 = [0, 368063465345, 1356202425720, 1869871022424, 1073040183970, 209038318113, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows5639 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5639 = true := by
  decide +kernel

theorem tot5639 : totK PA10K2 A10K2.t5639 = [0, 260403760671, 1389261406910, 2218538365339, 1096328432153, 107429783445, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
