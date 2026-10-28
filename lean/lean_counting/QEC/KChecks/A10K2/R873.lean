import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3492 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3492 = true := by
  decide +kernel

theorem tot3492 : totK PA10K2 A10K2.t3492 = [0, 0, 467365254010, 1790948303017, 2002210252275, 636674860537, 31049444317, 0, 0, 0] := by
  decide +kernel

theorem rows3493 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3493 = true := by
  decide +kernel

theorem tot3493 : totK PA10K2 A10K2.t3493 = [0, 0, 0, 580269259492, 1968558874621, 1774765375681, 413538568122, 25734533292, 0, 0] := by
  decide +kernel

theorem rows3494 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3494 = true := by
  decide +kernel

theorem tot3494 : totK PA10K2 A10K2.t3494 = [0, 0, 373418953322, 1340901568160, 1724940173149, 954686894294, 180892191761, 6034215561, 0, 0] := by
  decide +kernel

theorem rows3495 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3495 = true := by
  decide +kernel

theorem tot3495 : totK PA10K2 A10K2.t3495 = [0, 0, 448684272945, 1817829973936, 1999718195055, 535424883779, 26521581199, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
