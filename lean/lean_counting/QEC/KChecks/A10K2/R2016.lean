import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8064 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8064 = true := by
  decide +kernel

theorem tot8064 : totK PA10K2 A10K2.t8064 = [0, 0, 0, 539758633624, 1926311482847, 1834654723430, 460206516092, 25734533292, 0, 0] := by
  decide +kernel

theorem rows8065 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8065 = true := by
  decide +kernel

theorem tot8065 : totK PA10K2 A10K2.t8065 = [0, 0, 449094844100, 1648685440962, 1904955108034, 792217718856, 139595085605, 5809256573, 0, 0] := by
  decide +kernel

theorem rows8066 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8066 = true := by
  decide +kernel

theorem tot8066 : totK PA10K2 A10K2.t8066 = [0, 0, 109259794108, 977379050490, 1972181340250, 1398267373362, 374699558915, 26116334861, 0, 0] := by
  decide +kernel

theorem rows8067 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8067 = true := by
  decide +kernel

theorem tot8067 : totK PA10K2 A10K2.t8067 = [0, 0, 0, 591969447752, 2052741794622, 1884968427829, 405350689675, 13227942247, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
