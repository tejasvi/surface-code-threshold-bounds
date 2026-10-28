import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2120 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2120 = true := by
  decide +kernel

theorem tot2120 : totK PA10K2 A10K2.t2120 = [527310909255, 1924396823368, 1947130613692, 490345236951, 12244162943, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2121 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2121 = true := by
  decide +kernel

theorem tot2121 : totK PA10K2 A10K2.t2121 = [0, 615971307865, 1987190681446, 1762645945187, 419432350475, 25734533292, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2122 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2122 = true := by
  decide +kernel

theorem tot2122 : totK PA10K2 A10K2.t2122 = [192782041464, 981302108354, 1897104951768, 1356621699795, 232689148496, 6034215561, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2123 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2123 = true := by
  decide +kernel

theorem tot2123 : totK PA10K2 A10K2.t2123 = [555080580879, 1943562022396, 1819084095489, 472091849117, 26521581199, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
