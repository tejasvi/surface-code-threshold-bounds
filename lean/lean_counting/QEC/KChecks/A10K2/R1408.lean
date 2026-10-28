import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5632 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5632 = true := by
  decide +kernel

theorem tot5632 : totK PA10K2 A10K2.t5632 = [0, 320561472736, 898578194220, 980638615028, 1446776424986, 1235033361280, 248448880970, 6853348008, 0, 0] := by
  decide +kernel

theorem rows5633 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5633 = true := by
  decide +kernel

theorem tot5633 : totK PA10K2 A10K2.t5633 = [0, 496116447412, 1767462468104, 1893023268921, 555997773456, 32846095359, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5634 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5634 = true := by
  decide +kernel

theorem tot5634 : totK PA10K2 A10K2.t5634 = [0, 17059334586, 756456124005, 2047503604703, 1612571569639, 379209002797, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows5635 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5635 = true := by
  decide +kernel

theorem tot5635 : totK PA10K2 A10K2.t5635 = [0, 168952791685, 983088624745, 1918026882299, 1384142476953, 241329414796, 6034215561, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
