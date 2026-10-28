import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2268 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2268 = true := by
  decide +kernel

theorem tot2268 : totK PA10K2 A10K2.t2268 = [0, 236313805786, 938771483694, 1609025165300, 1458854716421, 549815618262, 41778035756, 0, 0, 0] := by
  decide +kernel

theorem rows2269 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2269 = true := by
  decide +kernel

theorem tot2269 : totK PA10K2 A10K2.t2269 = [0, 188041870025, 1240172069995, 2084693793000, 927470594834, 85943987110, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2270 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2270 = true := by
  decide +kernel

theorem tot2270 : totK PA10K2 A10K2.t2270 = [0, 544335039164, 1681356524474, 1717299944292, 738590930107, 127643692581, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows2271 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2271 = true := by
  decide +kernel

theorem tot2271 : totK PA10K2 A10K2.t2271 = [0, 258573709605, 1525152501261, 2269888485111, 895169787136, 74596148145, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
