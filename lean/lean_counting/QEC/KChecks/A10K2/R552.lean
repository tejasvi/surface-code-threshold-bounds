import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2208 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2208 = true := by
  decide +kernel

theorem tot2208 : totK PA10K2 A10K2.t2208 = [0, 520680832771, 1903589171446, 1931476609580, 529193078496, 31872591158, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2209 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2209 = true := by
  decide +kernel

theorem tot2209 : totK PA10K2 A10K2.t2209 = [0, 84539485306, 924560835716, 2140975538268, 1564096002715, 271252411947, 7047025452, 0, 0, 0] := by
  decide +kernel

theorem rows2210 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2210 = true := by
  decide +kernel

theorem tot2210 : totK PA10K2 A10K2.t2210 = [0, 300557247573, 1431579045326, 2149018645340, 924952549033, 74448197228, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2211 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2211 = true := by
  decide +kernel

theorem tot2211 : totK PA10K2 A10K2.t2211 = [0, 571956727054, 1972666187816, 1926500963553, 496832557686, 18513647723, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
