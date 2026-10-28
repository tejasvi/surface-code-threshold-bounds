import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3692 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3692 = true := by
  decide +kernel

theorem tot3692 : totK PA10K2 A10K2.t3692 = [0, 232933380217, 1426347813864, 2273932078201, 914350344085, 71531477741, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3693 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3693 = true := by
  decide +kernel

theorem tot3693 : totK PA10K2 A10K2.t3693 = [0, 0, 443702760245, 1805408809374, 1976623973537, 517988848810, 31768748853, 0, 0, 0] := by
  decide +kernel

theorem rows3694 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3694 = true := by
  decide +kernel

theorem tot3694 : totK PA10K2 A10K2.t3694 = [0, 483762212233, 1682913105384, 1825939057679, 715634342610, 78580078820, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3695 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3695 = true := by
  decide +kernel

theorem tot3695 : totK PA10K2 A10K2.t3695 = [0, 298064684126, 1512245211060, 2151147358619, 782109948560, 54566717916, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
