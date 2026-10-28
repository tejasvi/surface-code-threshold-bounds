import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows356 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t356 = true := by
  decide +kernel

theorem tot356 : totK PA10K2 A10K2.t356 = [0, 330722162075, 1160307086694, 1242091984864, 493069675971, 677941641675, 638237973995, 135399462593, 5976421810, 0] := by
  decide +kernel

theorem rows357 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t357 = true := by
  decide +kernel

theorem tot357 : totK PA10K2 A10K2.t357 = [0, 498898146768, 1886207460784, 1941082835680, 519812437241, 19435377505, 0, 0, 0, 0] := by
  decide +kernel

theorem rows358 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t358 = true := by
  decide +kernel

theorem tot358 : totK PA10K2 A10K2.t358 = [0, 0, 561316493966, 1970038270485, 1742242973380, 418650643760, 25371180993, 0, 0, 0] := by
  decide +kernel

theorem rows359 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t359 = true := by
  decide +kernel

theorem tot359 : totK PA10K2 A10K2.t359 = [0, 290616394563, 1269893560884, 1935320506522, 1134917208512, 192690055617, 5460492893, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
