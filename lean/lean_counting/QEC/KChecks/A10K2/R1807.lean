import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7228 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7228 = true := by
  decide +kernel

theorem tot7228 : totK PA10K2 A10K2.t7228 = [0, 474796662945, 1856711169548, 2107316482768, 616761741135, 33120803804, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7229 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7229 = true := by
  decide +kernel

theorem tot7229 : totK PA10K2 A10K2.t7229 = [0, 0, 597484755732, 2048188795224, 1860860334611, 398437587271, 13576218110, 0, 0, 0] := by
  decide +kernel

theorem rows7230 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7230 = true := by
  decide +kernel

theorem tot7230 : totK PA10K2 A10K2.t7230 = [0, 461050334078, 1670132001953, 2025688025371, 927155311029, 100931644689, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7231 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7231 = true := by
  decide +kernel

theorem tot7231 : totK PA10K2 A10K2.t7231 = [0, 365857935008, 1672027371040, 2238599471518, 831259658512, 44048804271, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
