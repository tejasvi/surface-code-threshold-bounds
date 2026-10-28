import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5792 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5792 = true := by
  decide +kernel

theorem tot5792 : totK PA10K2 A10K2.t5792 = [0, 0, 112109183544, 1251876398053, 2266205051145, 991378117463, 73630012816, 0, 0, 0] := by
  decide +kernel

theorem rows5793 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5793 = true := by
  decide +kernel

theorem tot5793 : totK PA10K2 A10K2.t5793 = [0, 0, 0, 568099606043, 1979945896484, 1739069353444, 404747382081, 26601763172, 0, 0] := by
  decide +kernel

theorem rows5794 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5794 = true := by
  decide +kernel

theorem tot5794 : totK PA10K2 A10K2.t5794 = [0, 0, 0, 473919598177, 1822500376378, 1995586811871, 471386725503, 18535904725, 0, 0] := by
  decide +kernel

theorem rows5795 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5795 = true := by
  decide +kernel

theorem tot5795 : totK PA10K2 A10K2.t5795 = [0, 0, 0, 549324792321, 1935660537184, 1796991274787, 390128638253, 25681272668, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
