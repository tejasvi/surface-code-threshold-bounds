import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8100 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8100 = true := by
  decide +kernel

theorem tot8100 : totK PA10K2 A10K2.t8100 = [0, 0, 0, 306766947263, 1476084419682, 2203548049321, 998078403988, 86659385911, 0, 0] := by
  decide +kernel

theorem rows8101 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8101 = true := by
  decide +kernel

theorem tot8101 : totK PA10K2 A10K2.t8101 = [0, 0, 0, 306389571234, 1280926227425, 1936576403694, 1192891997058, 205316203912, 6725424603, 0] := by
  decide +kernel

theorem rows8102 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8102 = true := by
  decide +kernel

theorem tot8102 : totK PA10K2 A10K2.t8102 = [0, 0, 0, 483448716589, 1877900625936, 2037500387943, 552423247019, 13048234710, 0, 0] := by
  decide +kernel

theorem rows8103 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8103 = true := by
  decide +kernel

theorem tot8103 : totK PA10K2 A10K2.t8103 = [0, 0, 0, 0, 577588347171, 2047155945240, 1860762800018, 350958886697, 12692412833, 0] := by
  decide +kernel

end QECKChecks.A10K2
