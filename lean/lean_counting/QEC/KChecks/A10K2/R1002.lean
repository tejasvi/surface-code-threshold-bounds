import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4008 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4008 = true := by
  decide +kernel

theorem tot4008 : totK PA10K2 A10K2.t4008 = [0, 0, 514818494382, 1972128284481, 2139970339047, 570113735262, 19876255495, 0, 0, 0] := by
  decide +kernel

theorem rows4009 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4009 = true := by
  decide +kernel

theorem tot4009 : totK PA10K2 A10K2.t4009 = [0, 525241347744, 1770491922368, 1663750133198, 584049030032, 231050343511, 37674914273, 0, 0, 0] := by
  decide +kernel

theorem rows4010 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4010 = true := by
  decide +kernel

theorem tot4010 : totK PA10K2 A10K2.t4010 = [0, 297779599935, 1459236426414, 2195245352274, 960215898081, 84571152217, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4011 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4011 = true := by
  decide +kernel

theorem tot4011 : totK PA10K2 A10K2.t4011 = [0, 0, 508731493782, 1866725938831, 1899100440000, 508963427935, 31768748853, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
