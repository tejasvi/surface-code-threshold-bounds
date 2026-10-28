import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3580 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3580 = true := by
  decide +kernel

theorem tot3580 : totK PA10K2 A10K2.t3580 = [0, 0, 504746463949, 1892384245406, 1824704068606, 443962006455, 26601763172, 0, 0, 0] := by
  decide +kernel

theorem rows3581 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3581 = true := by
  decide +kernel

theorem tot3581 : totK PA10K2 A10K2.t3581 = [0, 0, 529857969630, 1854715956729, 1964712636250, 521025975858, 18535904725, 0, 0, 0] := by
  decide +kernel

theorem rows3582 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3582 = true := by
  decide +kernel

theorem tot3582 : totK PA10K2 A10K2.t3582 = [0, 0, 495198898593, 1920777790758, 1929871157561, 437579501099, 26116334861, 0, 0, 0] := by
  decide +kernel

theorem rows3583 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3583 = true := by
  decide +kernel

theorem tot3583 : totK PA10K2 A10K2.t3583 = [0, 0, 512681511184, 1752152486212, 1826492013904, 545169261485, 45306140179, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
