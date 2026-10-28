import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows276 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t276 = true := by
  decide +kernel

theorem tot276 : totK PA10K2 A10K2.t276 = [0, 0, 0, 342061088711, 1594796316908, 1861692519153, 560841774787, 37883584371, 0, 0] := by
  decide +kernel

theorem rows277 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t277 = true := by
  decide +kernel

theorem tot277 : totK PA10K2 A10K2.t277 = [0, 0, 0, 295172554347, 1216838254438, 1825797046365, 965340760928, 162116493773, 5528811039, 0] := by
  decide +kernel

theorem rows278 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t278 = true := by
  decide +kernel

theorem tot278 : totK PA10K2 A10K2.t278 = [0, 0, 115487560146, 651889448038, 1772996573536, 1847966645591, 556679740387, 38394631736, 0, 0] := by
  decide +kernel

theorem rows279 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t279 = true := by
  decide +kernel

theorem tot279 : totK PA10K2 A10K2.t279 = [0, 0, 464356112785, 1890759396909, 1942542805806, 451099350342, 25686058060, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
