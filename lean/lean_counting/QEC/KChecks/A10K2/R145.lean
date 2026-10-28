import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows580 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t580 = true := by
  decide +kernel

theorem tot580 : totK PA10K2 A10K2.t580 = [0, 168648963668, 965878110273, 1920133087284, 1313482644959, 290029106011, 24614390653, 0, 0, 0] := by
  decide +kernel

theorem rows581 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t581 = true := by
  decide +kernel

theorem tot581 : totK PA10K2 A10K2.t581 = [0, 282958263264, 1179078674086, 1895970843597, 1158818183916, 177287303861, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows582 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t582 = true := by
  decide +kernel

theorem tot582 : totK PA10K2 A10K2.t582 = [0, 415775937008, 1691906177209, 1977796667178, 580971526598, 32846095359, 0, 0, 0, 0] := by
  decide +kernel

theorem rows583 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t583 = true := by
  decide +kernel

theorem tot583 : totK PA10K2 A10K2.t583 = [0, 0, 678716548652, 2043543994670, 1506879220495, 317738394950, 24969229125, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
