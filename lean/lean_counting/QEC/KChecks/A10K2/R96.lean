import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows384 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t384 = true := by
  decide +kernel

theorem tot384 : totK PA10K2 A10K2.t384 = [0, 542766534740, 1824244841811, 1870277255896, 656165169130, 60073280572, 0, 0, 0, 0] := by
  decide +kernel

theorem rows385 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t385 = true := by
  decide +kernel

theorem tot385 : totK PA10K2 A10K2.t385 = [0, 330854518425, 1547031597669, 2180024919332, 868902517372, 67445991918, 0, 0, 0, 0] := by
  decide +kernel

theorem rows386 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t386 = true := by
  decide +kernel

theorem tot386 : totK PA10K2 A10K2.t386 = [0, 0, 522991696666, 1944726641862, 1971831782652, 458389772051, 13816090359, 0, 0, 0] := by
  decide +kernel

theorem rows387 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t387 = true := by
  decide +kernel

theorem tot387 : totK PA10K2 A10K2.t387 = [0, 0, 589958023279, 1928358551601, 1852673493181, 571111851607, 49180423016, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
